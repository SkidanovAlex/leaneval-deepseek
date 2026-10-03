import Mathlib
import Submission.Work.Peluse.U2Inv.Defs

namespace Work.Peluse.U2Inv

/-- `DeltaZ a b f` is supported in `symIcc L` whenever `f` is: if `x ∉ symIcc L` then
`x.natAbs > L`, so `f x = 0` and the whole product vanishes. -/
lemma DeltaZ_eq_zero_of_not_mem_symIcc {L : ℕ} {f : ℤ → ℂ} (hf : Work.Peluse.SupportIn f L)
    (a b : ℤ) {x : ℤ} (hx : x ∉ Work.Peluse.symIcc L) : DeltaZ a b f x = 0 := by
  have hx' : L < x.natAbs := by
    rw [Work.Peluse.symIcc, Finset.mem_Icc] at hx
    omega
  simp [DeltaZ, hf x hx']

/-- The `tsum` over `ℤ` of `DeltaZ a b f (· + c)` is the finite sum of `DeltaZ a b f` over the
support `symIcc L`: the shift `· + c` is a bijection of `ℤ`, and `DeltaZ a b f` vanishes off
`symIcc L`.  This is the statement that the interval sum `T3` (defined with a `Finset` sum) is
the full `tsum` of the shift-corrected difference operator. -/
theorem u2inv_tsum_DeltaZ (L : ℕ) (f : ℤ → ℂ) (hf : Work.Peluse.SupportIn f L) (a b c : ℤ) :
    (∑' x : ℤ, Work.Peluse.U2Inv.DeltaZ a b f (x + c))
      = ∑ x ∈ Work.Peluse.symIcc L, Work.Peluse.U2Inv.DeltaZ a b f x := by
  have hshift : (∑' x : ℤ, Work.Peluse.U2Inv.DeltaZ a b f (x + c))
      = ∑' x : ℤ, Work.Peluse.U2Inv.DeltaZ a b f x := by
    simpa using Equiv.tsum_eq (Equiv.addRight c) (fun x => Work.Peluse.U2Inv.DeltaZ a b f x)
  rw [hshift]
  exact tsum_eq_sum fun x hx => DeltaZ_eq_zero_of_not_mem_symIcc hf a b hx

end Work.Peluse.U2Inv
