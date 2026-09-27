import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Core.uminus_entry_zero
import Submission.Work.EKLC6Core.contraction_rate_uminus

/-!
# `EKLC6Route.aDiag_conj_mem_V_of_mem_uminus`

The neighbourhood `V s = {g | maxᵢⱼ |gᵢⱼ - δᵢⱼ| < s}` of the identity is *invariant* under
conjugation by the powers of `aDiag t`, for elements `u` of the contracted subgroup
`Uminus t = ⨆_{t i < t j} U_ij` which already lie in `V s`:

`aDiag t ^ n · u · (aDiag t ^ n)⁻¹ ∈ V s`.

Equivalently: the diagonal flow shrinks such a `u` towards the identity, so one may keep the
*original* radius `s`.  The quantitative statement is
`Work.EKLC6Core.contraction_rate_uminus`: there is `α > 0` with
`aDiag t ^ n · u · (aDiag t ^ n)⁻¹ ∈ V (e^{-α n} ρ)` whenever `u ∈ Uminus t ∩ V ρ`.  Here we
only need that `e^{-α n} ρ ≤ ρ`, and that `V s ≠ ∅` forces `s > 0`.

This is the "shrinking" companion of `Work.EKLC6Route.aDiag_conj_mem_V_of_mem_VtSet`, which
covers the *expanding* subgroup `VtSet t` and therefore pays a factor `e^{n · betaExp t}` in the
radius.
-/

namespace Work.EKLC6Route

open Work.EKLContract

/-- If `u ∈ V s` then `s > 0` (so that `V s` is actually a nonempty ball). -/
theorem pos_of_mem_V {s : ℝ} {u : Work.EKLContract.SL3} (hu : u ∈ Work.EKLContract.V s) :
    0 < s := by
  have h := hu 0 0
  have h1 : (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 0 = 1 := Matrix.one_apply_eq 0
  rw [h1] at h
  have : 0 ≤ |(u : Matrix (Fin 3) (Fin 3) ℝ) 0 0 - 1| := abs_nonneg _
  linarith

/-- The balls `V s` are nested: `V s ⊆ V s'` when `0 < s ≤ s'`. -/
theorem V_subset_of_le {s s' : ℝ} (hss' : s ≤ s') :
    Work.EKLContract.V s ⊆ Work.EKLContract.V s' := by
  intro g hg i j
  exact lt_of_lt_of_le (hg i j) hss'

theorem aDiag_conj_mem_V_of_mem_uminus {t : Fin 3 → ℝ} {s : ℝ} {u : Work.EKLContract.SL3} (n : ℕ)
    (hu : u ∈ Work.EKLC6Core.Uminus t) (huV : u ∈ Work.EKLContract.V s) :
    Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹ ∈
      Work.EKLContract.V s := by
  -- `u ∈ V s` forces `s > 0`, so the contraction estimate may be run at radius `s`
  have hs : 0 < s := pos_of_mem_V huV
  -- the uniform contraction rate on `Uminus t`
  obtain ⟨α, hαpos, hα⟩ := Work.EKLC6Core.contraction_rate_uminus t
  have hmem : Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹ ∈
      Work.EKLContract.V (Real.exp (-(α * (n : ℝ))) * s) := hα n s hs u hu huV
  -- and the radius only shrinks: `e^{-α n} s ≤ s`
  refine V_subset_of_le ?_ hmem
  have hexp : Real.exp (-(α * (n : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ α * (n : ℝ) := mul_nonneg hαpos.le (Nat.cast_nonneg n)
    linarith
  calc Real.exp (-(α * (n : ℝ))) * s ≤ 1 * s := mul_le_mul_of_nonneg_right hexp hs.le
    _ = s := one_mul s

end Work.EKLC6Route
