import Mathlib

/-!
# Reindexing lemma for the `resS` row sums (`Work.ResMath.resS_rowsum_reindex`)

Paper Harvey–van der Hoeven, *Integer multiplication in time* `O(n log n)`, Thm 4.2 / §4.2
step (c): the double sum over the row index `j : Fin s` and the integer shift `q : ℤ` of the
Gaussian `exp (-(π s²/α²) (z - j/s - q)²)` is the single sum over `n : ℤ` of
`exp (-(π/α²) (s z - n)²)`.

The point is that the map `(j,q) ↦ j + s q` is a bijection `Fin s × ℤ → ℤ` (division with
remainder, `Int.divModEquiv`), and after multiplying the argument of the Gaussian by `s`,
`z - j/s - q = (s z - (j + s q))/s`, so the Gaussian prefactor changes from `π s²/α²` to
`π/α²` accordingly.  No Poisson summation is involved: this is pure reindexing of an
absolutely convergent (indeed positive) family.
-/

set_option linter.style.haveILetI false

namespace Work.ResMath

theorem resS_rowsum_reindex (s : ℕ) (hs : 0 < s) (α : ℝ) (hα : 0 < α) (z : ℝ) :
    ∑ j : Fin s, ∑' q : ℤ,
        Real.exp (-(Real.pi * (s : ℝ) ^ 2 / α ^ 2) * (z - (j : ℝ) / (s : ℝ) - (q : ℝ)) ^ 2)
      = ∑' n : ℤ, Real.exp (-(Real.pi / α ^ 2) * (s * z - (n : ℝ)) ^ 2) := by
  haveI : NeZero s := ⟨hs.ne'⟩
  -- The summand of the right-hand side is summable (Gaussian decay on `ℤ`).
  have hfsum :
      Summable (fun n : ℤ => Real.exp (-(Real.pi / α ^ 2) * (s * z - (n : ℝ)) ^ 2)) := by
    have h := HurwitzKernelBounds.summable_f_int 0 (-(s * z)) (show (0 : ℝ) < 1 / α ^ 2 by positivity)
    refine h.congr (fun n => ?_)
    simp only [HurwitzKernelBounds.f_int, pow_zero, one_mul]
    congr 1
    have hαne : α ≠ 0 := ne_of_gt hα
    field_simp
    ring
  -- The bijection `(j,q) ↦ j + s q` between `Fin s × ℤ` and `ℤ`.
  set e : Fin s × ℤ ≃ ℤ := (Equiv.prodComm (Fin s) ℤ).trans (Int.divModEquiv s).symm with he
  have heval : ∀ (j : Fin s) (q : ℤ), e (j, q) = (j : ℤ) + (s : ℤ) * q := by
    intro j q
    rw [he]
    simp [Int.divModEquiv_symm_apply, mul_comm, add_comm]
  -- Pointwise identification of the summands.
  have hterm : ∀ (j : Fin s) (q : ℤ),
      Real.exp (-(Real.pi * (s : ℝ) ^ 2 / α ^ 2) * (z - (j : ℝ) / (s : ℝ) - (q : ℝ)) ^ 2)
        = Real.exp (-(Real.pi / α ^ 2) * ((s : ℝ) * z - (e (j, q) : ℝ)) ^ 2) := by
    intro j q
    rw [heval j q]
    have h1 : (((j : ℤ) + (s : ℤ) * q : ℤ) : ℝ) = (j : ℝ) + (s : ℝ) * (q : ℝ) := by
      push_cast; ring
    rw [h1]
    have h2 : ((s : ℝ) * z - ((j : ℝ) + (s : ℝ) * (q : ℝ)))
        = (s : ℝ) * (z - (j : ℝ) / (s : ℝ) - (q : ℝ)) := by
      field_simp; ring
    rw [h2, mul_pow]
    congr 1
    field_simp
  -- Summability transfers to the reindexed family.
  have hecomp :
      Summable (fun p : Fin s × ℤ =>
        Real.exp (-(Real.pi / α ^ 2) * ((s : ℝ) * z - (e p : ℝ)) ^ 2)) :=
    (Equiv.summable_iff
      (f := fun n : ℤ => Real.exp (-(Real.pi / α ^ 2) * ((s : ℝ) * z - (n : ℝ)) ^ 2)) e).mpr hfsum
  calc ∑ j : Fin s, ∑' q : ℤ,
          Real.exp (-(Real.pi * (s : ℝ) ^ 2 / α ^ 2) * (z - (j : ℝ) / (s : ℝ) - (q : ℝ)) ^ 2)
      = ∑' j : Fin s, ∑' q : ℤ,
          Real.exp (-(Real.pi * (s : ℝ) ^ 2 / α ^ 2) * (z - (j : ℝ) / (s : ℝ) - (q : ℝ)) ^ 2) :=
        (tsum_fintype _).symm
    _ = ∑' j : Fin s, ∑' q : ℤ,
          Real.exp (-(Real.pi / α ^ 2) * ((s : ℝ) * z - (e (j, q) : ℝ)) ^ 2) :=
        tsum_congr (fun j => tsum_congr (fun q => hterm j q))
    _ = ∑' p : Fin s × ℤ,
          Real.exp (-(Real.pi / α ^ 2) * ((s : ℝ) * z - (e p : ℝ)) ^ 2) :=
        (Summable.tsum_prod hecomp).symm
    _ = ∑' n : ℤ, Real.exp (-(Real.pi / α ^ 2) * ((s : ℝ) * z - (n : ℝ)) ^ 2) :=
        Equiv.tsum_eq e (fun n : ℤ => Real.exp (-(Real.pi / α ^ 2) * ((s : ℝ) * z - (n : ℝ)) ^ 2))

end Work.ResMath
