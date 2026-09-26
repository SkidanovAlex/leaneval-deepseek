/-
# The `S`-transport laws of the kernel and of the cusp models, without `ETailE_one`

`Submission/Work/Asymptotics/ETailE_one.lean` imports the sharp funnel statement
`Work.Asymptotics.Khat_funnel_tail_sharp` (which is proved from the `Kdev` development in
`Submission/Work/Asymptotics/KhatE1/`).  The `Kdev` development, in turn, needs the two
`S`-transport laws `Kfun(S•τ,z) = -τ^{d/2}K̂(τ,z)` and `𝒢(S•τ,z) = -τ^{d/2}(𝒢₊-𝒢₋)(τ,z)/2`
in order to pass between the funnel and the cusp-`0` tile.  Importing `ETailE_one` for them
would create an import cycle, so they are reproduced here, in the auxiliary namespace
`Work.Asymptotics.KhatE1.STPure`, with the same statements and proofs.
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Compact.gfun_eq
import Submission.Work.Kernels.KMinusSlash
import Submission.Work.Asymptotics.EtailE.EtailE_KPlus8
import Submission.Work.Asymptotics.EtailE.EtailE_KPlus24
import Submission.Work.Asymptotics.EtailE.Atoms

namespace Work.Asymptotics.KhatE1.STPure

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups

open Work.Kernels

lemma coe_S_smul (τ : ℍ) : ((ModularGroup.S • τ : ℍ) : ℂ) = -((τ : ℂ))⁻¹ := by
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]

lemma phi1_S_smul (τ : ℍ) : Compact.phi1 (ModularGroup.S • τ) = -Compact.phi1 τ := by
  have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  unfold Compact.phi1
  rw [Work.Kernels.E2Fun_S_smul τ, coe_S_smul τ]
  field_simp
  ring

lemma phi2t_S_smul (τ : ℍ) :
    Compact.phi2t (ModularGroup.S • τ) = -((τ : ℂ) ^ 2) * Compact.phi2t τ := by
  have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  unfold Compact.phi2t
  rw [Work.Kernels.E2Fun_S_smul τ, coe_S_smul τ]
  field_simp
  ring

lemma E8Fun_S (τ : ℍ) : E8Fun (ModularGroup.S • τ) = (τ : ℂ) ^ 8 * E8Fun τ := by
  simp only [E8Fun, EtailE.E4Fun_S τ]
  ring

lemma E10Fun_S (τ : ℍ) : E10Fun (ModularGroup.S • τ) = (τ : ℂ) ^ 10 * E10Fun τ := by
  simp only [E10Fun, EtailE.E4Fun_S τ, EtailE.E6Fun_S τ]
  ring

lemma E14Fun_S (τ : ℍ) : E14Fun (ModularGroup.S • τ) = (τ : ℂ) ^ 14 * E14Fun τ := by
  simp only [E14Fun, EtailE.E4Fun_S τ, EtailE.E6Fun_S τ]
  ring

lemma Gminus8_S_smul (ℓ : LogLambdaData) (τ z : ℍ) :
    Compact.Gminus8 ℓ (ModularGroup.S • τ) z = (τ : ℂ) ^ 4 * Compact.Gminus8 ℓ τ z := by
  have hτ0 : (τ : ℂ) ≠ 0
  · exact τ.ne_zero
  simp only [Compact.Gminus8]
  rw [EtailE.E4Fun_S τ, EtailE.psi4_S ℓ τ]
  ring

lemma Gminus24_S_smul (ℓ : LogLambdaData) (τ z : ℍ) :
    Compact.Gminus24 ℓ (ModularGroup.S • τ) z = (τ : ℂ) ^ 12 * Compact.Gminus24 ℓ τ z := by
  have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hD0 : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hE0 : Work.Residues.Ept z ≠ 0 := Work.Residues.Ept_ne_zero z
  simp only [Compact.Gminus24]
  rw [E8Fun_S τ, E10Fun_S τ, EtailE.DeltaFun_Ssmul τ,
      EtailE.jInvariantFun_Ssmul τ, EtailE.psi2_S ℓ τ, EtailE.psi4_S ℓ τ]
  ring

/-- **The `S`-law of the cusp model `𝒢₊`.** -/
theorem Gplus_S_smul (d : ℕ) (hd : d = 8 ∨ d = 24) (τ z : ℍ) :
    Compact.Gplus d (ModularGroup.S • τ) z = -((τ : ℂ) ^ ((d : ℤ) / 2)) * Compact.Gplus d τ z := by
  rcases hd with h | h
  · subst h
    rw [show (((8 : ℕ) : ℤ) / 2) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast]
    simp only [Compact.Gplus, if_true]
    exact EtailE.Gplus8_S_smul τ z
  · subst h
    rw [show (((24 : ℕ) : ℤ) / 2) = ((12 : ℕ) : ℤ) by norm_num, zpow_natCast]
    simp only [Compact.Gplus, if_neg (by decide : ¬ ((24 : ℕ) = 8))]
    exact EtailE.Gplus24_S_smul τ z

/-- **The `S`-law of the cusp model `𝒢₋`.** -/
theorem Gminus_S_smul (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ z : ℍ) :
    Compact.Gminus d ℓ (ModularGroup.S • τ) z
      = (τ : ℂ) ^ ((d : ℤ) / 2) * Compact.Gminus d ℓ τ z := by
  rcases hd with h | h
  · subst h
    rw [show (((8 : ℕ) : ℤ) / 2) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast]
    simp only [Compact.Gminus, if_true]
    exact Gminus8_S_smul ℓ τ z
  · subst h
    rw [show (((24 : ℕ) : ℤ) / 2) = ((12 : ℕ) : ℤ) by norm_num, zpow_natCast]
    simp only [Compact.Gminus, if_neg (by decide : ¬ ((24 : ℕ) = 8))]
    exact Gminus24_S_smul ℓ τ z

/-- **The `S`-law of the cusp model `𝒢 = (𝒢₊ + 𝒢₋)/2`.** -/
theorem Gfun_S_smul (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ z : ℍ) :
    Compact.Gfun d ℓ (ModularGroup.S • τ) z
      = -((τ : ℂ) ^ ((d : ℤ) / 2)) * (Compact.Gplus d τ z - Compact.Gminus d ℓ τ z) / 2 := by
  have h := Compact.gfun_eq ℓ d hd (ModularGroup.S • τ) z
  rw [Gplus_S_smul d hd τ z, Gminus_S_smul ℓ d hd τ z] at h
  have h2 : 2 * Compact.Gfun d ℓ (ModularGroup.S • τ) z
      = -((τ : ℂ) ^ ((d : ℤ) / 2)) * (Compact.Gplus d τ z - Compact.Gminus d ℓ τ z) := by
    rw [← h]; ring
  refine (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).mpr ?_
  rw [mul_comm]
  exact h2

/-- **The `S`-transport of the kernel `K̂`.** -/
theorem Khat_eq_neg_slash_pointwise (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ τ z : ℍ, Khat ℓ d τ z
      = - (τ : ℂ) ^ (-((d : ℤ) / 2)) * Kfun ℓ d (ModularGroup.S • τ) z := by
  intro τ z
  have h := congr_fun (Khat_eq_neg_slash ℓ d hd z) τ
  rw [h, slash_apply']
  have hj : jFun ModularGroup.S (τ : ℂ) = (τ : ℂ) := by
    rw [jFun_apply]; simp
  rw [hj]
  ring

theorem Kfun_S_smul (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ z : ℍ) :
    Kfun ℓ d (ModularGroup.S • τ) z = - (τ : ℂ) ^ ((d : ℤ) / 2) * Khat ℓ d τ z := by
  have h := Khat_eq_neg_slash_pointwise ℓ d hd τ z
  have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hk : (τ : ℂ) ^ (-((d : ℤ) / 2)) * (τ : ℂ) ^ ((d : ℤ) / 2) = 1 := by
    rw [← zpow_add₀ hτ0]; simp
  calc Kfun ℓ d (ModularGroup.S • τ) z
      = ((τ : ℂ) ^ (-((d : ℤ) / 2)) * (τ : ℂ) ^ ((d : ℤ) / 2))
          * Kfun ℓ d (ModularGroup.S • τ) z := by rw [hk, one_mul]
    _ = (τ : ℂ) ^ ((d : ℤ) / 2)
          * ((τ : ℂ) ^ (-((d : ℤ) / 2)) * Kfun ℓ d (ModularGroup.S • τ) z) := by ring
    _ = (τ : ℂ) ^ ((d : ℤ) / 2) * (-(Khat ℓ d τ z)) := by rw [h]; ring
    _ = - (τ : ℂ) ^ ((d : ℤ) / 2) * Khat ℓ d τ z := by ring

theorem Kfun_S_smul_eight (ℓ : LogLambdaData) (τ z : ℍ) :
    Kfun ℓ 8 (ModularGroup.S • τ) z = - (τ : ℂ) ^ 4 * Khat ℓ 8 τ z := by
  have h := Kfun_S_smul ℓ 8 (Or.inl rfl) τ z
  rw [show (((8 : ℕ) : ℤ) / 2) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast] at h
  exact h

theorem Kfun_S_smul_twentyfour (ℓ : LogLambdaData) (τ z : ℍ) :
    Kfun ℓ 24 (ModularGroup.S • τ) z = - (τ : ℂ) ^ 12 * Khat ℓ 24 τ z := by
  have h := Kfun_S_smul ℓ 24 (Or.inr rfl) τ z
  rw [show (((24 : ℕ) : ℤ) / 2) = ((12 : ℕ) : ℤ) by norm_num, zpow_natCast] at h
  exact h

theorem Gfun_S_smul_twentyfour (ℓ : LogLambdaData) (τ z : ℍ) :
    Compact.Gfun 24 ℓ (ModularGroup.S • τ) z
      = - (τ : ℂ) ^ 12 * (Compact.Gplus 24 τ z - Compact.Gminus 24 ℓ τ z) / 2 := by
  have h := Gfun_S_smul ℓ 24 (Or.inr rfl) τ z
  rw [show (((24 : ℕ) : ℤ) / 2) = ((12 : ℕ) : ℤ) by norm_num, zpow_natCast] at h
  exact h

end Work.Asymptotics.KhatE1.STPure
