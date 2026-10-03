import Mathlib
import Submission.Work.Peluse.Basic

/-!
# The fibres of the map `(a, a') ↦ a - a'` on `[m] × [m]`

Peluse's weight `μ_m` is the distribution of the difference of two independent uniform points of
`[m] = {1, …, m}`: `μ_m(α) = #{a, a' ∈ [m] : a - a'} / m²`.  Consequently the sum of `Y (a - a')`
over all pairs `(a, a') ∈ [m]²` is the `μ_m`-weighted sum of `Y` over the differences
`α ∈ [-（m-1), m-1]`, scaled by `m²`:

`∑_{a, a' ∈ [m]} Y (a - a') = m² ∑_{α ∈ [-(m-1), m-1]} μ_m(α) Y(α)`.

This is the "fibre" identity of the `U²`-inverse argument (Peluse, *Bounds for sets with no
polynomial progressions*, Forum Math. Pi **8** (2020), Lemma 2.4): it rewrites the interval box
sum of a `Δ`-weighted average as a genuine average over the shift variable `α`, which is what
allows the van der Corput / Fourier argument to proceed.
-/

open scoped BigOperators

namespace Work.Peluse.U2Inv

noncomputable section

/-- Reindex a sum over `arithIcc 1 m = {1, …, m} ⊂ ℤ` as a sum over `Finset.Icc 1 m ⊂ ℕ`. -/
private lemma sum_arithIcc_one (m : ℕ) (F : ℤ → ℂ) :
    (∑ a ∈ Work.Peluse.arithIcc 1 m, F a) = ∑ n ∈ Finset.Icc 1 m, F (n : ℤ) := by
  rw [Work.Peluse.arithIcc]
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl (fun n _ => ?_)
    simp
  · intro x _ y _ h
    simpa using h

/-- The double sum over `arithIcc 1 m × arithIcc 1 m` as a sum over the product finset
`(Finset.Icc 1 m) ×ˢ (Finset.Icc 1 m)` of the difference. -/
private lemma sum_arithIcc_sq_eq (m : ℕ) (Y : ℤ → ℂ) :
    (∑ a ∈ Work.Peluse.arithIcc 1 m, ∑ a' ∈ Work.Peluse.arithIcc 1 m, Y (a - a'))
      = ∑ p ∈ (Finset.Icc 1 m).product (Finset.Icc 1 m), Y ((p.1 : ℤ) - (p.2 : ℤ)) := by
  simp only [sum_arithIcc_one]
  exact (Finset.sum_product (Finset.Icc 1 m) (Finset.Icc 1 m)
    (fun p : ℕ × ℕ => Y ((p.1 : ℤ) - (p.2 : ℤ)))).symm

/-- Fibre decomposition of a sum over a product finset: if the difference map
`(p.1, p.2) ↦ p.1 - p.2` maps `S` into `T`, then the sum of `Y` over `S` is the sum over the
fibres of the difference, weighted by their sizes. -/
private lemma sum_fiberwise_eq (S : Finset (ℕ × ℕ)) (T : Finset ℤ) (Y : ℤ → ℂ)
    (hD : ∀ p ∈ S, ((p.1 : ℤ) - (p.2 : ℤ)) ∈ T) :
    (∑ p ∈ S, Y ((p.1 : ℤ) - (p.2 : ℤ)))
      = ∑ α ∈ T, (((S.filter (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = α)).card : ℕ) : ℂ)
          * Y α := by
  calc ∑ p ∈ S, Y ((p.1 : ℤ) - (p.2 : ℤ))
      = ∑ p ∈ S, ∑ α ∈ T, (if (p.1 : ℤ) - (p.2 : ℤ) = α then Y α else 0) := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [Finset.sum_ite_eq, if_pos (hD p hp)]
    _ = ∑ α ∈ T, ∑ p ∈ S, (if (p.1 : ℤ) - (p.2 : ℤ) = α then Y α else 0) :=
        Finset.sum_comm
    _ = ∑ α ∈ T, ∑ p ∈ S.filter (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = α), Y α := by
        refine Finset.sum_congr rfl (fun α _ => ?_)
        rw [Finset.sum_filter]
    _ = ∑ α ∈ T, (((S.filter (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = α)).card : ℕ) : ℂ)
          * Y α := by
        refine Finset.sum_congr rfl (fun α _ => ?_)
        rw [Finset.sum_const, nsmul_eq_mul]

/-- The defining relation of the weight `μ_m`: for `m ≥ 1`,
`m² · μ_m(α) = #{p ∈ [m]² : p.1 - p.2 = α}`. -/
private lemma mul_muL_eq_card (m : ℕ) (hm : 1 ≤ m) (α : ℤ) :
    ((m : ℂ) ^ 2) * (Work.Peluse.muL m α : ℂ)
      = ((((Finset.Icc 1 m).product (Finset.Icc 1 m)).filter
          (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = α)).card : ℂ) := by
  have hmC : (m : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : m ≠ 0)
  rw [Work.Peluse.muL]
  rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow]
  rw [Complex.ofReal_natCast, Complex.ofReal_natCast]
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hmC), one_mul]

theorem u2inv_muL_fiber (m : ℕ) (Y : ℤ → ℂ) :
    (∑ a ∈ Work.Peluse.arithIcc 1 m, ∑ a' ∈ Work.Peluse.arithIcc 1 m, Y (a - a'))
      = ((m : ℂ) ^ 2) * ∑ α ∈ Work.Peluse.symIcc (m - 1),
          (Work.Peluse.muL m α : ℂ) * Y α := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    simp [Work.Peluse.arithIcc]
  · -- the difference of two points of `[m]²` lies in the support interval of `μ_m`
    have hDmem : ∀ p ∈ (Finset.Icc 1 m).product (Finset.Icc 1 m),
        ((p.1 : ℤ) - (p.2 : ℤ)) ∈ Work.Peluse.symIcc (m - 1) := by
      intro p hp
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
      obtain ⟨h1a, h1b⟩ := Finset.mem_Icc.mp h1
      obtain ⟨h2a, h2b⟩ := Finset.mem_Icc.mp h2
      have hm1 : 1 ≤ m := le_trans h1a h1b
      have hcast : (((m - 1 : ℕ)) : ℤ) = (m : ℤ) - 1 := by
        rw [Nat.cast_sub hm1]; norm_num
      rw [Work.Peluse.symIcc, Finset.mem_Icc, hcast]
      constructor <;> omega
    have hsum := sum_fiberwise_eq ((Finset.Icc 1 m).product (Finset.Icc 1 m))
      (Work.Peluse.symIcc (m - 1)) Y hDmem
    calc (∑ a ∈ Work.Peluse.arithIcc 1 m, ∑ a' ∈ Work.Peluse.arithIcc 1 m, Y (a - a'))
        = ∑ p ∈ (Finset.Icc 1 m).product (Finset.Icc 1 m), Y ((p.1 : ℤ) - (p.2 : ℤ)) :=
          sum_arithIcc_sq_eq m Y
      _ = ∑ α ∈ Work.Peluse.symIcc (m - 1),
            ((((Finset.Icc 1 m).product (Finset.Icc 1 m)).filter
              (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = α)).card : ℂ) * Y α := hsum
      _ = ((m : ℂ) ^ 2) * ∑ α ∈ Work.Peluse.symIcc (m - 1),
            (Work.Peluse.muL m α : ℂ) * Y α := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun α _ => ?_)
          rw [← mul_muL_eq_card m hmpos α, mul_assoc]

end

end Work.Peluse.U2Inv
