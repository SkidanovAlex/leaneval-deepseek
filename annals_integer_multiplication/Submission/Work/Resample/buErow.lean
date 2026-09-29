import Mathlib
import Submission.Work.Resample.sliceB1defs
import Submission.Work.ResMath.Nmat_apply
import Submission.Work.ResMath.summable_Nsum
import Submission.Work.ResMath.resE_row

namespace Work.Resample

open HvdH

/-- The `n`-th summand `phi s t α hs ℓ x n` of the `Nmat` row series is the displacement-`h`
term of the Gaussian series over `h = n - ℓ`, i.e. `egW` times `x` at the reduced index. -/
lemma phi_eq_egW (s t α : ℕ) (hs : 0 < s) (ℓ : Fin s) (x : Fin s → ℂ) (n : ℤ) :
    Work.ResMath.phi s t α hs ℓ x n
      = ((egW s t α (ℓ : ℤ) (n - (ℓ : ℤ)) : ℝ) : ℂ)
          * x (egIdx s hs ((ℓ : ℤ) + (n - (ℓ : ℤ)))) := by
  simp only [Work.ResMath.phi, Work.Resample.egW, Work.Resample.egIdx]
  have h1 : ((ℓ : ℤ)) + (n - (ℓ : ℤ)) = n := by ring
  rw [h1]
  congr 1
  rw [Complex.ofReal_inj]
  congr 1
  push_cast
  ring

/-- The ℓ-th row of `E = Nmat - 1` is the Gaussian series over the displacement `h`:
`(E x)_ℓ = ∑'_{h ≠ 0} W(ℓ,h) x((ℓ+h) mod s)` with `W(ℓ,h) = exp(-πα²((th/s+β_ℓ)² - β_{ℓ+h}²))`.

NOTE (for the prover): `Submission.Work.ResMath.resE_row` (which contains `Nmat_mulVec_eq_tsum`)
does NOT currently compile, so do not import it. Instead use `Work.ResMath.Nmat_apply`
(`Nmat s t α ℓ j = (∑'_q exp(-πα²(tq + t(j-ℓ)/s + β_ℓ)²)) * exp(πα²β_j²)`, which builds fine) and
regroup the entries of the row sum by the displacement `h = j - ℓ + m*s` (the entry with
displacement `h` is `egW s t α ℓ h`) — equivalently reindex the double sum
`∑_j ∑_q` by the bijection `(j,q) ↦ ℓ + j - ℓ + q*s` of `Fin s × ℤ` onto `ℤ`. -/
theorem buErow (s t α : ℕ) (hs : 0 < s) (hst : s < t) (hα : 0 < α)
    (ℓ : Fin s) (x : Fin s → ℂ) :
    ((HvdH.Emat s t α).mulVec x) ℓ
      = ∑' h : ℤ, (if h = 0 then 0 else
          ((Work.Resample.egW s t α (ℓ : ℤ) h : ℝ) : ℂ) * x (Work.Resample.egIdx s hs ((ℓ : ℤ) + h))) := by
  set f : ℤ → ℂ := fun h => ((egW s t α (ℓ : ℤ) h : ℝ) : ℂ)
    * x (egIdx s hs ((ℓ : ℤ) + h)) with hf
  have hphi : ∀ n : ℤ, Work.ResMath.phi s t α hs ℓ x n = f (n - (ℓ : ℤ)) := by
    intro n
    rw [hf]
    exact phi_eq_egW s t α hs ℓ x n
  have hsumm_n : Summable (fun n : ℤ => Work.ResMath.phi s t α hs ℓ x n) :=
    Work.ResMath.summable_phi s t α hs hst hα x ℓ
  have hsumm_f : Summable f := by
    have h : Summable (fun n : ℤ => f (n - (ℓ : ℤ))) := hsumm_n.congr (fun n => hphi n)
    have h' : Summable (fun n : ℤ => f ((Equiv.subRight (ℓ : ℤ)) n)) := by
      simpa [Equiv.subRight_apply] using h
    exact (Equiv.summable_iff (Equiv.subRight (ℓ : ℤ)) (f := f)).mp h'
  have htsum : (∑' n : ℤ, Work.ResMath.phi s t α hs ℓ x n) = ∑' h : ℤ, f h := by
    rw [tsum_congr hphi]
    simpa [Equiv.subRight_apply] using Equiv.tsum_eq (Equiv.subRight (ℓ : ℤ)) f
  have hf0 : f 0 = x ℓ := by
    have h1 : f ((ℓ : ℤ) - (ℓ : ℤ)) = x ℓ := by
      rw [← hphi (ℓ : ℤ), Work.ResMath.phi_self]
    simpa using h1
  have hEm : ((HvdH.Emat s t α).mulVec x) ℓ = (HvdH.Nmat s t α).mulVec x ℓ - x ℓ := by
    rw [HvdH.Emat, Matrix.sub_mulVec, Matrix.one_mulVec]
    rfl
  rw [hEm, Work.ResMath.Nmat_mulVec_eq_tsum s t α hs hst hα x ℓ, htsum,
    hsumm_f.tsum_eq_add_tsum_ite (0 : ℤ), hf0]
  ring

end Work.Resample
