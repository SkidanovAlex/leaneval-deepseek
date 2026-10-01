import Mathlib
import Submission.Work.ZeroDensity.Jutila.sieveSymbolDefs
import Submission.Work.LinnikAreas.Density4.SelbergDefs
import Submission.Work.ZeroDensity.Jutila.sieveU_expansion

/-!
# The coprime Möbius reciprocal sum expanded along the `l`-smooth numbers

`Work.ZeroDensity.Jutila.U y l = Σ_{m ≤ y, (m,l) = 1} μ(m)/m` is the Möbius reciprocal
sum restricted to the integers coprime to `l`.  Its expansion along the `l`-smooth numbers
reads

`U y l = Σ_{d ≤ y, d l-smooth} (1/d) · Σ_{k ≤ y/d} μ(k)/k`,

where a number is `l`-smooth when every one of its prime factors divides `l`
(`SmoothOf d l ↔ d ∣ l ^ d`).  Equivalently, in Dirichlet-series language, the identity is
the coefficient-wise form of

`Π_{p ∤ l} (1 - p^{-s}) = (Σ_{rad d ∣ l} d^{-s}) · (1/ζ(s))`.

The content is the Möbius-inversion identity
`μ(n)·[(n,l) = 1] = Σ_{d ∣ n, d l-smooth} μ(n/d)`, summed against `1/n` and reindexed by
`n = d·k`.
-/

namespace Work.LinnikAreas.JutilaPieces

open Finset

/-- The radical divisibility `rad d ∣ l` agrees with the smoothness predicate `SmoothOf d l`
(which is `d ∣ l ^ d`, i.e. "every prime factor of `d` divides `l`") for `d ≠ 0`. -/
theorem rad_dvd_iff_smoothOf {d l : ℕ} (hd : d ≠ 0) :
    Work.ZeroDensity.Jutila.rad d ∣ l ↔ Work.LinnikAreas.Density4.SmoothOf d l := by
  rw [Work.LinnikAreas.Density4.smoothOf_iff_prime_dvd hd]
  constructor
  · intro h p hp hpd
    have hprad : p ∣ Work.ZeroDensity.Jutila.rad d := by
      rw [Work.ZeroDensity.Jutila.rad]
      exact Finset.dvd_prod_of_mem (fun q : ℕ => q)
        (Nat.mem_primeFactors.mpr ⟨hp, hpd, hd⟩)
    exact hprad.trans h
  · intro h
    rcases eq_or_ne l 0 with hl | hl
    · subst hl
      exact dvd_zero _
    · rw [Work.ZeroDensity.Jutila.rad, Nat.prod_primeFactors_dvd_iff hl]
      intro p hp
      obtain ⟨hp', hpd, _⟩ := Nat.mem_primeFactors.mp hp
      exact Nat.mem_primeFactors.mpr ⟨hp', h p hp' hpd, hl⟩

/-- At `l = 1` the coprimality filter in `U` is vacuous, so `U t 1` is the plain Möbius
reciprocal sum `muRecipSum t`. -/
theorem U_one_eq_muRecipSum (t : ℕ) :
    Work.ZeroDensity.Jutila.U t 1 = Commons.NumberTheory.Moebius.muRecipSum t := by
  rw [Work.ZeroDensity.Jutila.U, Commons.NumberTheory.Moebius.muRecipSum]
  apply Finset.sum_congr _ (fun m _ => rfl)
  ext m
  simp

theorem U_eq (y l : ℕ) (hl : 1 ≤ l) :
    Work.ZeroDensity.Jutila.U y l
      = ∑ d ∈ (Finset.Icc 1 y).filter (fun d => Work.LinnikAreas.Density4.SmoothOf d l),
          (1 / (d : ℝ)) * Commons.NumberTheory.Moebius.muRecipSum (y / d) := by
  -- `U` expanded along the `rad`-divisibility condition.
  rw [Work.ZeroDensity.Jutila.sieveU_expansion y l hl]
  refine Finset.sum_congr ?_ ?_
  · -- `rad d ∣ l` and `SmoothOf d l` agree on the range `1 ≤ d`.
    apply Finset.filter_congr
    intro d hdmem
    have hd0 : d ≠ 0 := Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hdmem).1
    exact rad_dvd_iff_smoothOf hd0
  · -- at the second argument `1`, `U` is the Möbius reciprocal sum `muRecipSum`.
    intro d _
    rw [U_one_eq_muRecipSum]

end Work.LinnikAreas.JutilaPieces
