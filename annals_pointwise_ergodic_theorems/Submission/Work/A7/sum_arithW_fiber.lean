/-
# Regrouping a sum against the `q`-periodic arithmetic character `arithW` (Area A7)

The arithmetic character `arithW P α₁ α₂ n = fourier n α₁ · fourier (P n) α₂` is `q`-periodic
on `ℤ` as soon as `q • α₁ = q • α₂ = 0` (`arithW_period_mul`).  Consequently a sum
`∑_{K < n ≤ N} arithW n · V n` can be reorganised by the residue class of `n` modulo `q`: on each
fibre `n % q = a` the factor `arithW` is the constant `arithW a`, and it pulls out of the inner
sum.  This is the bookkeeping step used when the discrete average is compared with the arithmetic
average `mZ` over the residue classes mod `q`.
-/
import Mathlib
import Submission.Work.A7.ModelApproxCore_M0_defs

namespace Work.A7

theorem sum_arithW_fiber (P : Polynomial ℤ) (q : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle)
    (hq : 0 < q) (h₁ : q • α₁ = 0) (h₂ : q • α₂ = 0) (K N : ℕ) (V : ℕ → ℂ) :
    (∑ n ∈ Finset.Ioc K N, arithW P α₁ α₂ (n : ℤ) * V n)
      = ∑ a ∈ Finset.range q,
          arithW P α₁ α₂ (a : ℤ) * ∑ n ∈ (Finset.Ioc K N).filter (fun n => n % q = a), V n := by
  -- split the interval into the fibres of `n ↦ n % q`, which all land in `range q`
  have hmod : ∀ n ∈ Finset.Ioc K N, n % q ∈ Finset.range q :=
    fun n _ => Finset.mem_range.mpr (Nat.mod_lt n hq)
  have hpart := Finset.sum_fiberwise_of_maps_to hmod (fun n => arithW P α₁ α₂ (n : ℤ) * V n)
  rw [← hpart]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  -- on each fibre `arithW` is the constant `arithW a`, so it pulls out of the inner sum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Finset.mem_filter] at hn
  obtain ⟨hnS, hna⟩ := hn
  -- `n = a + q * (n / q)`, so periodicity gives `arithW n = arithW a`
  have hkey : (n : ℤ) = (a : ℤ) + q * ((n / q : ℕ) : ℤ) := by
    have h := Nat.div_add_mod n q
    rw [hna] at h
    have h' : ((q * (n / q) + a : ℕ) : ℤ) = (n : ℤ) := by exact_mod_cast h
    rw [Nat.cast_add, Nat.cast_mul] at h'
    linarith
  rw [hkey, arithW_period_mul P q α₁ α₂ h₁ h₂ (a : ℤ) ((n / q : ℕ) : ℤ)]

end Work.A7
