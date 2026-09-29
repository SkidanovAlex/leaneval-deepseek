import Mathlib
import Submission.Work.ResMath.defs

/-!
# Definitions for the `Emat` norm bound (`Work.ResMath.resE_norm_le`)

This module collects the definitions and elementary facts used by the proof of
`Work.ResMath.resE_norm_le`, i.e. of Lemma 4.6 of Harvey–van der Hoeven, *Integer multiplication
in time* `O(n log n)` (Annals 193 (2021)), in the formalisation of `Submission/HvdH/Interfaces.lean`.

* `betaI s t n` is `β_n = tn/s - ⌊tn/s + 1/2⌋` for an arbitrary integer index `n`
  (the paper's `β_ℓ = tℓ/s - [tℓ/s]` is the special case `n = ℓ : ℕ`);
* `rndI s t ℓ` is the row index `[tℓ/s]` of the `ℓ`-th row of the row-deleting map `C`.
-/

namespace Work.ResMath

open HvdH

/-- `β` as a function of an arbitrary integer index: `β_n = tn/s - ⌊tn/s + 1/2⌋`. -/
noncomputable def betaI (s t : ℕ) (n : ℤ) : ℝ := ((t : ℝ) * (n : ℝ)) / s - ⌊((t : ℝ) * (n : ℝ)) / s + 1 / 2⌋

/-- `β` on natural indices agrees with `HvdH.betaR`. -/
lemma betaI_eq_betaR (s t : ℕ) (ℓ : ℕ) : betaI s t (ℓ : ℤ) = HvdH.betaR s t ℓ := by
  simp [betaI, HvdH.betaR, HvdH.rnd]

/-- `β` is periodic of period `s`. -/
lemma betaI_dvd_shift (s t : ℕ) (hs : 0 < s) (n : ℤ) (k : ℤ) :
    betaI s t (n + s * k) = betaI s t n := by
  have hs' : (s : ℝ) ≠ 0 := by positivity
  have h1 : ((t : ℝ) * ((n + s * k : ℤ) : ℝ)) / s = ((t : ℝ) * (n : ℝ)) / s + (t : ℝ) * k := by
    push_cast
    field_simp
  rw [betaI, betaI, h1]
  have h2 : ⌊((t : ℝ) * (n : ℝ)) / s + (t : ℝ) * k + 1 / 2⌋
      = ⌊((t : ℝ) * (n : ℝ)) / s + 1 / 2⌋ + (t : ℝ) * k := by
    have h3 := Int.floor_add_intCast (((t : ℝ) * (n : ℝ)) / s + 1 / 2) ((t : ℤ) * k)
    rw [show ((t : ℝ) * (n : ℝ)) / s + (t : ℝ) * k + 1 / 2
        = ((t : ℝ) * (n : ℝ)) / s + 1 / 2 + (((t : ℤ) * k : ℤ) : ℝ) by push_cast; ring, h3]
    push_cast
    ring
  rw [h2]
  ring

/-- `|β_n| ≤ 1/2`. -/
lemma betaI_abs_le (s t : ℕ) (n : ℤ) : |betaI s t n| ≤ 1 / 2 := by
  have h1 : (⌊((t : ℝ) * (n : ℝ)) / s + 1 / 2⌋ : ℝ) ≤ ((t : ℝ) * (n : ℝ)) / s + 1 / 2 :=
    Int.floor_le _
  have h2 : ((t : ℝ) * (n : ℝ)) / s + 1 / 2 < (⌊((t : ℝ) * (n : ℝ)) / s + 1 / 2⌋ : ℝ) + 1 :=
    Int.lt_floor_add_one _
  rw [betaI, abs_le]
  constructor <;> linarith

/-- The row index `[tℓ/s]` of the `ℓ`-th row of the row-deleting map `C`. -/
noncomputable def rndI (s t : ℕ) (ℓ : Fin s) : ℤ := HvdH.rnd ((t * ℓ : ℝ) / s)

lemma rndI_def (s t : ℕ) (ℓ : Fin s) : rndI s t ℓ = ⌊(t * ℓ : ℝ) / s + 1 / 2⌋ := rfl

/-- The row index `[tℓ/s]` is in `{0, …, t-1}` when `2 ≤ s < t`. -/
lemma rndI_mem (s t : ℕ) (hs : 0 < s) (hst : s < t) (ℓ : Fin s) :
    0 ≤ rndI s t ℓ ∧ rndI s t ℓ < t := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hst' : (s : ℝ) < t := by exact_mod_cast hst
  have ht : (1 : ℝ) < (t : ℝ) / s := by
    rw [lt_div_iff₀ hs']
    simpa using hst'
  have hℓ : ((ℓ : ℝ)) ≤ (s : ℝ) - 1 := by
    have h : (ℓ : ℕ) + 1 ≤ s := ℓ.isLt
    have h' : ((ℓ : ℕ) : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast h
    linarith
  constructor
  · rw [rndI_def]; exact Int.floor_nonneg.mpr (by positivity)
  · rw [rndI_def, Int.floor_lt]
    push_cast
    have hkey : ((t : ℝ) / s) * (ℓ : ℝ) ≤ ((t : ℝ) / s) * ((s : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hℓ (by positivity)
    have hexp : ((t : ℝ) / s) * ((s : ℝ) - 1) = (t : ℝ) - (t : ℝ) / s := by
      field_simp
    have h1 : (t : ℝ) - (t : ℝ) / s < (t : ℝ) - 1 := by linarith
    have h2 : (t : ℝ) * (ℓ : ℝ) / s = ((t : ℝ) / s) * (ℓ : ℝ) := by ring
    linarith

/-- The representative of `ℓ + h` in `{0, …, s-1}`, as an element of `Fin s`. -/
noncomputable def modIdx (s : ℕ) (hs : 0 < s) (ℓ : Fin s) (h : ℤ) : Fin s :=
  ⟨(((ℓ : ℤ) + h) % s).toNat, by
    have hs' : (s : ℤ) ≠ 0 := by omega
    have h1 : 0 ≤ ((ℓ : ℤ) + h) % s := Int.emod_nonneg _ hs'
    have h2 : ((ℓ : ℤ) + h) % s < s := Int.emod_lt_of_pos _ (by omega)
    have h3 : ((((ℓ : ℤ) + h) % s).toNat : ℤ) = ((ℓ : ℤ) + h) % s := Int.toNat_of_nonneg h1
    have : ((((ℓ : ℤ) + h) % s).toNat : ℤ) < (s : ℤ) := by rw [h3]; exact h2
    exact_mod_cast this⟩

lemma modIdx_coe (s : ℕ) (hs : 0 < s) (ℓ : Fin s) (h : ℤ) :
    ((modIdx s hs ℓ h : ℕ) : ℤ) = ((ℓ : ℤ) + h) % s := by
  have hs' : (s : ℤ) ≠ 0 := by omega
  have h1 : 0 ≤ ((ℓ : ℤ) + h) % s := Int.emod_nonneg _ hs'
  have h3 : ((((ℓ : ℤ) + h) % s).toNat : ℤ) = ((ℓ : ℤ) + h) % s := Int.toNat_of_nonneg h1
  simpa [modIdx] using h3

/-- `β` depends only on the residue class mod `s` of its (integer) argument. -/
lemma betaI_modIdx (s t : ℕ) (hs : 0 < s) (ℓ : Fin s) (h : ℤ) :
    betaI s t ((modIdx s hs ℓ h : ℕ) : ℤ) = betaI s t ((ℓ : ℤ) + h) := by
  rw [modIdx_coe]
  conv_rhs => rw [← Int.emod_add_mul_ediv ((ℓ : ℤ) + h) (s : ℤ)]
  exact (betaI_dvd_shift s t hs _ _).symm

/-- The `(j,q)` summand in the `q`-series defining an entry of the `ℓ`-th row of `Nmat`. -/
noncomputable def Nsum (s t α : ℕ) (ℓ : Fin s) (u : Fin s → ℂ) (j : Fin s) (q : ℤ) : ℂ :=
  ((Real.exp (-(Real.pi * (α : ℝ) ^ 2 *
      ((t : ℝ) * (q : ℝ) + (t : ℝ) * ((j : ℤ) - (ℓ : ℤ)) / (s : ℝ) + betaI s t (ℓ : ℤ)) ^ 2)) : ℝ) : ℂ)
    * ((Real.exp (Real.pi * (α : ℝ) ^ 2 * (HvdH.betaR s t j) ^ 2) : ℝ) : ℂ) * u j

/-- The representative of `n` modulo `s` in `{0, …, s-1}`, as an element of `Fin s`. -/
noncomputable def modZ (s : ℕ) (hs : 0 < s) (n : ℤ) : Fin s :=
  ⟨(n % s).toNat, by
    have hs' : (s : ℤ) ≠ 0 := by omega
    have h1 : 0 ≤ n % s := Int.emod_nonneg _ hs'
    have h2 : n % s < s := Int.emod_lt_of_pos _ (by omega)
    have h3 : ((n % s).toNat : ℤ) = n % s := Int.toNat_of_nonneg h1
    have : ((n % s).toNat : ℤ) < (s : ℤ) := by rw [h3]; exact h2
    exact_mod_cast this⟩

lemma modZ_coe (s : ℕ) (hs : 0 < s) (n : ℤ) : ((modZ s hs n : ℕ) : ℤ) = n % s := by
  have hs' : (s : ℤ) ≠ 0 := by omega
  have h1 : 0 ≤ n % s := Int.emod_nonneg _ hs'
  simpa [modZ] using Int.toNat_of_nonneg h1

lemma modZ_eq_self (s : ℕ) (hs : 0 < s) (j : Fin s) : modZ s hs (j : ℤ) = j := by
  have h : ((modZ s hs (j : ℤ) : ℕ) : ℤ) = ((j : ℕ) : ℤ) := by
    rw [modZ_coe]
    exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast j.isLt)
  exact Fin.ext (Nat.cast_injective h)

lemma modZ_add_mul (s : ℕ) (hs : 0 < s) (n : ℤ) (k : ℤ) :
    modZ s hs (n + s * k) = modZ s hs n := by
  have h : ((modZ s hs (n + s * k) : ℕ) : ℤ) = ((modZ s hs n : ℕ) : ℤ) := by
    rw [modZ_coe, modZ_coe, Int.add_mul_emod_self_left]
  exact Fin.ext (Nat.cast_injective h)

/-- The `n`-th summand of the `ℓ`-th row of `Nmat`, with `n = j + q s` ranging over `ℤ`; this is
the form appearing in Lemma 4.6 of Harvey–van der Hoeven:
`(Nu)_ℓ = Σ_n e^{-πα²((t(n-ℓ)/s+β_ℓ)² - β_n²)} u_{n mod s}`. -/
noncomputable def phi (s t α : ℕ) (hs : 0 < s) (ℓ : Fin s) (u : Fin s → ℂ) (n : ℤ) : ℂ :=
  ((Real.exp (-(Real.pi * (α : ℝ) ^ 2 *
      (((t : ℝ) * ((n : ℝ) - (ℓ : ℝ)) / s + betaI s t (ℓ : ℤ)) ^ 2 - (betaI s t n) ^ 2))) : ℝ) : ℂ)
    * u (modZ s hs n)

end Work.ResMath
