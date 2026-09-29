import Mathlib
import Submission.Work.Resample.sliceB1defs

/-!
# `Work.Resample.buPerm`

The two permutation facts behind the one-dimensional resampling word `B̃`
(paper Prop. 4.7(ii), used by `Submission/Work/Resample/sliceB1.lean`):

* the composite `C̃ ∘ P̃_t` maps the `ℓ`-th output to the `ν ℓ`-th input,
  `ν ℓ = σ_t [tℓ/s]`;
* the transposed permutation `P̃_sᵀ` maps the `j`-th output to the `γ j`-th input,
  where `γ j` is the source index of the final `P̃_sᵀ` step.

Both are statements about the matrices `HvdH.rowSel`, `HvdH.permT`, `HvdH.permS` of
`Submission/HvdH/Interfaces.lean`; the only arithmetic input is that the integer row index
`[tℓ/s] = ⌊tℓ/s + 1/2⌋` of `HvdH.rowSel` (there called `HvdH.rnd`) coincides with the natural
quotient `(2tℓ+s)/(2s)` used by `Work.Resample.egRho`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ## The rounding index

`HvdH.rnd x = ⌊x + 1/2⌋`, so the row index selected by `C̃` is `⌊tℓ/s + 1/2⌋`; the definition
`egRho` realises this by the *natural* quotient `(2tℓ+s)/(2s)`.  The two agree because the
Nat–division of naturals coincides with the integer floor of the corresponding real quotient
(`Int.floor_div_natCast`, `Int.natCast_div`). -/

/-- `egRho` is the integer rounding `[tℓ/s]` of `HvdH.rowSel`, cast back to `ℕ`. -/
lemma egRho_cast_rnd (t s n : ℕ) (hs : 0 < s) :
    ((egRho s t n : ℕ) : ℤ) = HvdH.rnd ((t : ℝ) * (n : ℝ) / (s : ℝ)) := by
  have hmain : ((2 * t * n + s : ℕ) : ℝ) / ((2 * s : ℕ) : ℝ)
      = (t : ℝ) * (n : ℝ) / (s : ℝ) + 1 / 2 := by
    push_cast
    field_simp
  rw [HvdH.rnd, ← hmain, Work.Resample.egRho]
  rw [Int.floor_div_natCast, Int.floor_natCast]
  exact (Int.natCast_div _ _).symm

/-- `egRho s t ℓ` is the `ℕ`-value of the row index `rndI s t ℓ` of `C̃`. -/
lemma egRho_rndI (s t : ℕ) (hs : 0 < s) (ℓ : Fin s) :
    egRho s t (ℓ : ℕ) = (Work.ResMath.rndI s t ℓ).toNat := by
  have h := egRho_cast_rnd t s (ℓ : ℕ) hs
  have hrnd : Work.ResMath.rndI s t ℓ = ((egRho s t (ℓ : ℕ) : ℕ) : ℤ) := by
    rw [Work.ResMath.rndI]; exact h.symm
  have hge : (0 : ℤ) ≤ Work.ResMath.rndI s t ℓ := by
    rw [hrnd]; exact Int.natCast_nonneg _
  exact Nat.cast_injective (by rw [Int.toNat_of_nonneg hge, ← hrnd])

/-! ## The entries of the two permutation matrices -/

/-- The entry `(ℓ,i)` of `C̃ ∘ P̃_t = rowSel * permT` is `1` exactly at `i = ν ℓ = egNu s t ℓ`:
`rowSel` picks the column `k = [tℓ/s] ∈ {0,…,t-1}` and `permT` then picks `σ_t k`. -/
lemma rowSel_mul_permT_apply (s t : ℕ) (hs : 0 < s) (hst : s < t) (ℓ : Fin s) (i : Fin t) :
    ((HvdH.rowSel s t) * (HvdH.permT s t)) ℓ i
      = (if (i : ℕ) = egNu s t (ℓ : ℕ) then 1 else 0) := by
  obtain ⟨h0, hlt⟩ := Work.ResMath.rndI_mem s t hs hst ℓ
  have htoNat : (((Work.ResMath.rndI s t ℓ).toNat : ℕ) : ℤ) = Work.ResMath.rndI s t ℓ :=
    Int.toNat_of_nonneg h0
  let k0 : Fin t := ⟨(Work.ResMath.rndI s t ℓ).toNat, by omega⟩
  have hk0val : (k0 : ℕ) = (Work.ResMath.rndI s t ℓ).toNat := rfl
  have hk0Z : ((k0 : ℕ) : ℤ) = Work.ResMath.rndI s t ℓ := by rw [hk0val]; exact htoNat
  have hk0rho : (k0 : ℕ) = egRho s t (ℓ : ℕ) := by
    rw [hk0val]; exact (egRho_rndI s t hs ℓ).symm
  rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem k0 (Finset.mem_univ k0)]
  · rw [show HvdH.rowSel s t ℓ k0
          = (if ((k0 : ℕ) : ℤ) = Work.ResMath.rndI s t ℓ then 1 else 0) from rfl,
      ite_eq_left hk0Z, one_mul]
    rw [HvdH.permT, hk0rho]
    rfl
  · intro b _ hb
    rw [show HvdH.rowSel s t ℓ b
          = (if ((b : ℕ) : ℤ) = Work.ResMath.rndI s t ℓ then 1 else 0) from rfl]
    have hbZ : ¬ (((b : ℕ) : ℤ) = Work.ResMath.rndI s t ℓ) := by
      intro h
      exact hb (Fin.ext (by have h1 : (b : ℕ) = (k0 : ℕ) := by omega
                            exact h1))
    rw [ite_eq_right hbZ, zero_mul]

/-- The entry `(j,i)` of `P̃_sᵀ = (permS s t)ᵀ` is `1` exactly at `i = γ j = egGam s t j`; this is
the injectivity (`egKeyS_inj`) plus the defining property (`egGam_spec`) of the index map
`i ↦ (t i) mod s`. -/
lemma permS_transpose_apply (s t : ℕ) (hs : 0 < s) (hcop : Nat.Coprime t s) (j i : Fin s) :
    (HvdH.permS s t).transpose j i = (if i = egGam s t hs hcop j then 1 else 0) := by
  rw [Matrix.transpose_apply]
  simp only [HvdH.permS]
  by_cases h : i = egGam s t hs hcop j
  · subst h
    have hc : (j : ℕ) = t * ((egGam s t hs hcop j : Fin s) : ℕ) % s := by
      change (j : ℕ) = egKeyS s t ((egGam s t hs hcop j : Fin s) : ℕ)
      rw [egGam_spec]
    rw [ite_eq_left hc]
    simp
  · have hc : ¬ ((j : ℕ) = t * (i : ℕ) % s) := by
      intro hj
      have h1 : egKeyS s t (i : ℕ) = egKeyS s t ((egGam s t hs hcop j : Fin s) : ℕ) := by
        rw [egGam_spec]
        change t * (i : ℕ) % s = (j : ℕ)
        exact hj.symm
      exact h (Fin.ext (egKeyS_inj s t hs hcop i.isLt (egGam s t hs hcop j).isLt h1))
    rw [ite_eq_right hc, ite_eq_right h]

/-! ## The target -/

theorem buPerm (s t : ℕ) (hs : 0 < s) (hst : s < t) (hcop : Nat.Coprime t s)
    (x : Fin t → ℂ) (v : Fin s → ℂ) (ℓ : Fin s) (j : Fin s) :
    (((HvdH.rowSel s t) * (HvdH.permT s t)).mulVec x) ℓ = HvdH.vget x (Work.Resample.egNu s t (ℓ : ℕ)) ∧
    (((HvdH.permS s t).transpose).mulVec v) j = v (Work.Resample.egGam s t hs hcop j) := by
  constructor
  · -- `C̃ ∘ P̃_t` picks out the `ν ℓ`-th coordinate
    have hN : egNu s t (ℓ : ℕ) < t := by
      have ht : 0 < t := lt_trans hs hst
      simp only [Work.Resample.egNu, Work.Resample.egSigT]
      exact Nat.mod_lt _ ht
    rw [HvdH.vget, dite_eq_left hN]
    conv_lhs => rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single (⟨egNu s t (ℓ : ℕ), hN⟩ : Fin t)]
    · rw [rowSel_mul_permT_apply s t hs hst ℓ ⟨egNu s t (ℓ : ℕ), hN⟩]
      simp
    · intro b _ hb
      rw [rowSel_mul_permT_apply s t hs hst ℓ b]
      have hb' : ¬ ((b : ℕ) = egNu s t (ℓ : ℕ)) := fun h => hb (Fin.ext h)
      rw [ite_eq_right hb', zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- `P̃_sᵀ` picks out the `γ j`-th coordinate
    conv_lhs => rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single (egGam s t hs hcop j)]
    · rw [permS_transpose_apply s t hs hcop j, ite_eq_left rfl]
      simp
    · intro b _ hb
      rw [permS_transpose_apply s t hs hcop j b]
      rw [ite_eq_right hb, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

end Work.Resample
