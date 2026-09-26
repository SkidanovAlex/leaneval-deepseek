import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.gfun_eq
import Submission.Work.Asymptotics.CuspExp.Models
import Submission.Work.Asymptotics.EtailE.Basic
import Submission.Work.Asymptotics.EtailE.Atoms
import Submission.Work.Kernels.KMinusSlash
import Submission.Work.Asymptotics.Khat_funnel_tail_sharp

/-!
# The cusp-`i∞` tail of the kernel on the cusp-`0` tile `E = KEpsilon`

The target `Work.Asymptotics.ETailE_one` is one of the two analytic inputs of the two-regime
bound `Work.Asymptotics.ERegimes` on `E`: for `w ∈ E` and `t ≥ scale w` the kernel
`Kaxis (Kfun ℓ d) w t` differs from the cusp model `Aexp (Gcusp ℓ d) w t` by
`O((scale w)^N t^M e^{-π t})`.

This file reduces that statement to the *funnel* form of it (the sharp tail of `K̂`), which is
the form in which the analytic work is done.  Write `τ = S • w ∈ 𝔽 = Funnel` for `w ∈ E`; the
structural facts are

* `Khat ℓ d τ z = -(τ)⁻ᵈᐟ² Kfun ℓ d (S • τ) z` (the `S`-transport in the `τ` variable,
  from `Khat_eq_neg_slash`), so that `Kfun(S • τ, z) = -(τ)ᵈᐟ² Khat(τ,z)`;
* the same `S`-law for the cusp models, `𝒢₊(S • τ, z) = -τᵈᐟ² 𝒢₊(τ,z)` and
  `𝒢₋(S • τ, z) = τᵈᐟ² 𝒢₋(τ,z)`, which together with `gfun_eq` gives
  `𝒢(S • τ, z) = -τᵈᐟ² (𝒢₊(τ,z) - 𝒢₋(τ,z))/2`;
* `scale(S • w) ≥ Im(S • w) + 1` and `‖S • w‖ ≤ scale w`, `scale(S • w) ≤ 3 scale w`.

Since `Aexp (Gcusp ℓ d) w t = 𝒢 d ℓ w (it)` (`Gcusp = Gcoef` and `AexpZ_imagAxis`), the
`E`-statement is *equivalent* to `Khat_funnel_tail_sharp`.
-/

noncomputable section

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics

open Work.Kernels

/-! ## §1  `Aexp (Gcusp ℓ d)` is the cusp model `Gfun d ℓ` on the imaginary axis -/

lemma qParamFun_eq_Ept_sq' (z : ℍ) : qParamFun z = Work.Residues.Ept z ^ 2 := by
  unfold qParamFun Work.Residues.Ept
  rw [sq, ← Complex.exp_add]
  congr 1
  ring

lemma Gcusp8_eq_Gcoef8 (ℓ : LogLambdaData) (i j : Fin 2) (τ : ℍ) :
    Gcusp8 ℓ i j τ = (Compact.Gcoef 8 ℓ) i j τ := by
  have h : (Compact.Gcoef 8 ℓ) i j τ
      = if i = 1 then 0
        else if j = 0 then
          (-Complex.I * (τ : ℂ) * E6Fun τ
            + (E4Fun τ * Compact.cuspC ℓ - psi4 ℓ τ / 2) / (Real.pi : ℂ)) / 2
        else
          ((Real.pi : ℂ) / 3 * ((τ : ℂ) * E6Fun τ - Compact.phi1 τ * E4Fun τ)
            + Complex.I * E4Fun τ) / 2 := by
    rw [Compact.Gcoef]; simp
  rw [h]
  simp only [Gcusp8]
  rw [show phiVec τ 0 = (τ : ℂ) from rfl,
      show phiVec τ 1 = Compact.phi1 τ from rfl,
      show cuspL ℓ = Compact.cuspC ℓ from rfl]
  split_ifs <;> ring_nf

lemma Gcusp24_eq_Gcoef24 (ℓ : LogLambdaData) {d : ℕ} (h8 : ¬ d = 8) (i j : Fin 2) (τ : ℍ) :
    Gcusp24 ℓ i j τ = (Compact.Gcoef d ℓ) i j τ := by
  rw [Compact.Gcoef, if_neg h8]
  simp only [Gcusp24]
  rw [show phiVec τ 0 = (τ : ℂ) from rfl,
      show phiVec τ 1 = Compact.phi1 τ from rfl,
      show phiVec τ 2 = Compact.phi2t τ from rfl,
      show cuspL ℓ = Compact.cuspC ℓ from rfl]
  try (split_ifs <;> ring_nf)

/-- The cusp coefficient functions `Gcusp ℓ d` and `Compact.Gcoef d ℓ` are the same. -/
theorem Gcusp_eq_Gcoef_one (ℓ : LogLambdaData) (d : ℕ) :
    Gcusp ℓ d = Compact.Gcoef d ℓ := by
  by_cases h8 : d = 8
  · subst h8
    funext i j τ
    exact Gcusp8_eq_Gcoef8 ℓ i j τ
  · funext i j τ
    rw [Gcusp, if_neg h8]
    exact Gcusp24_eq_Gcoef24 ℓ h8 i j τ

lemma inv_sq_eq_zpow' (a : ℂ) : (a ^ 2)⁻¹ = a ^ (-2 : ℤ) := by
  rw [show (-2 : ℤ) = -((2 : ℤ)) by norm_num, _root_.zpow_neg, zpow_ofNat]

lemma AexpZ_Gcoef_eq_Gfun (ℓ : LogLambdaData) (d : ℕ) (τ z : ℍ) :
    AexpZ (Compact.Gcoef d ℓ) τ z = Compact.Gfun d ℓ τ z := by
  unfold AexpZ Compact.Gfun mq
  rw [qParamFun_eq_Ept_sq', inv_sq_eq_zpow']

/-- `Aexp (Gcusp ℓ d) w t` is the cusp model `Gfun d ℓ` evaluated at `it`. -/
theorem Aexp_Gcusp_eq_Gfun (ℓ : LogLambdaData) (d : ℕ) (w : ℍ) (t : ℝ) (ht : 0 < t) :
    Aexp (Gcusp ℓ d) w t = Compact.Gfun d ℓ w (imagAxis t ht) := by
  rw [← AexpZ_imagAxis (Gcusp ℓ d) w t ht]
  rw [Gcusp_eq_Gcoef_one ℓ d]
  exact AexpZ_Gcoef_eq_Gfun ℓ d w (imagAxis t ht)

/-! ## §2  The `S`-laws of the `τ`-atoms and of the cusp models -/

lemma coe_S_smul_one (τ : ℍ) : ((ModularGroup.S • τ : ℍ) : ℂ) = -((τ : ℂ))⁻¹ := by
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]

lemma phi1_S_smul (τ : ℍ) : Compact.phi1 (ModularGroup.S • τ) = -Compact.phi1 τ := by
  have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  unfold Compact.phi1
  rw [Work.Kernels.E2Fun_S_smul τ, coe_S_smul_one τ]
  field_simp
  ring

lemma phi2t_S_smul (τ : ℍ) :
    Compact.phi2t (ModularGroup.S • τ) = -((τ : ℂ) ^ 2) * Compact.phi2t τ := by
  have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  unfold Compact.phi2t
  rw [Work.Kernels.E2Fun_S_smul τ, coe_S_smul_one τ]
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

lemma Gplus8_S_smul (τ z : ℍ) :
    Compact.Gplus8 (ModularGroup.S • τ) z = -((τ : ℂ) ^ 4) * Compact.Gplus8 τ z := by
  have hτ0 : (τ : ℂ) ≠ 0
  · exact τ.ne_zero
  simp only [Compact.Gplus8]
  rw [EtailE.E4Fun_S τ, EtailE.E6Fun_S τ, phi1_S_smul τ, coe_S_smul_one τ]
  field_simp
  ring

lemma Gminus8_S_smul (ℓ : LogLambdaData) (τ z : ℍ) :
    Compact.Gminus8 ℓ (ModularGroup.S • τ) z = (τ : ℂ) ^ 4 * Compact.Gminus8 ℓ τ z := by
  have hτ0 : (τ : ℂ) ≠ 0
  · exact τ.ne_zero
  simp only [Compact.Gminus8]
  rw [EtailE.E4Fun_S τ, EtailE.psi4_S ℓ τ]
  ring

lemma Gplus24_S_smul (τ z : ℍ) :
    Compact.Gplus24 (ModularGroup.S • τ) z = -((τ : ℂ) ^ 12) * Compact.Gplus24 τ z := by
  have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hD0 : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hE0 : Work.Residues.Ept z ≠ 0 := Work.Residues.Ept_ne_zero z
  simp only [Compact.Gplus24]
  rw [EtailE.E4Fun_S τ, E10Fun_S τ, E14Fun_S τ, EtailE.DeltaFun_Ssmul τ,
      EtailE.jInvariantFun_Ssmul τ, phi1_S_smul τ, phi2t_S_smul τ, coe_S_smul_one τ]
  field_simp
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
    exact Gplus8_S_smul τ z
  · subst h
    rw [show (((24 : ℕ) : ℤ) / 2) = ((12 : ℕ) : ℤ) by norm_num, zpow_natCast]
    simp only [Compact.Gplus, if_neg (by decide : ¬ ((24 : ℕ) = 8))]
    exact Gplus24_S_smul τ z

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

/-! ## §3  The `S`-transport of the kernel `K̂` -/

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

/-- `Kfun(S • τ, z) = -τ⁴ K̂(τ,z)` in dimension `8`. -/
theorem Kfun_S_smul_eight (ℓ : LogLambdaData) (τ z : ℍ) :
    Kfun ℓ 8 (ModularGroup.S • τ) z = - (τ : ℂ) ^ 4 * Khat ℓ 8 τ z := by
  have h := Kfun_S_smul ℓ 8 (Or.inl rfl) τ z
  rw [show (((8 : ℕ) : ℤ) / 2) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast] at h
  exact h

/-- `Kfun(S • τ, z) = -τ¹² K̂(τ,z)` in dimension `24`. -/
theorem Kfun_S_smul_twentyfour (ℓ : LogLambdaData) (τ z : ℍ) :
    Kfun ℓ 24 (ModularGroup.S • τ) z = - (τ : ℂ) ^ 12 * Khat ℓ 24 τ z := by
  have h := Kfun_S_smul ℓ 24 (Or.inr rfl) τ z
  rw [show (((24 : ℕ) : ℤ) / 2) = ((12 : ℕ) : ℤ) by norm_num, zpow_natCast] at h
  exact h

/-- `Gfun 8 ℓ (S • τ, z) = -τ⁴ (𝒢₊(τ,z) - 𝒢₋(τ,z))/2`. -/
theorem Gfun_S_smul_eight (ℓ : LogLambdaData) (τ z : ℍ) :
    Compact.Gfun 8 ℓ (ModularGroup.S • τ) z
      = - (τ : ℂ) ^ 4 * (Compact.Gplus 8 τ z - Compact.Gminus 8 ℓ τ z) / 2 := by
  have h := Gfun_S_smul ℓ 8 (Or.inl rfl) τ z
  rw [show (((8 : ℕ) : ℤ) / 2) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast] at h
  exact h

/-- `Gfun 24 ℓ (S • τ, z) = -τ¹² (𝒢₊(τ,z) - 𝒢₋(τ,z))/2`. -/
theorem Gfun_S_smul_twentyfour (ℓ : LogLambdaData) (τ z : ℍ) :
    Compact.Gfun 24 ℓ (ModularGroup.S • τ) z
      = - (τ : ℂ) ^ 12 * (Compact.Gplus 24 τ z - Compact.Gminus 24 ℓ τ z) / 2 := by
  have h := Gfun_S_smul ℓ 24 (Or.inr rfl) τ z
  rw [show (((24 : ℕ) : ℤ) / 2) = ((12 : ℕ) : ℤ) by norm_num, zpow_natCast] at h
  exact h

/-! ## §4  Elementary scale estimates on `E = KEpsilon` -/

/-- On `E`, the `S`-image has height at most `scale w - 1`: `Im (S • w) + 1 ≤ scale w`. -/
lemma im_S_smul_add_one_le_scale (w : ℍ) : (ModularGroup.S • w).im + 1 ≤ scale w := by
  have h1 : (ModularGroup.S • w).im = w.im / ‖(w : ℂ)‖ ^ 2 := EtailE.E_im_S w
  have hsq : w.im ^ 2 ≤ ‖(w : ℂ)‖ ^ 2 := EtailE.im_sq_le_normSq w
  have hpos : 0 < w.im := w.im_pos
  have hwpos : 0 < ‖(w : ℂ)‖ := norm_pos_iff.mpr w.ne_zero
  have h6 : w.im ≤ ‖(w : ℂ)‖ ^ 2 / w.im := by
    rw [le_div_iff₀ hpos]; nlinarith [hsq]
  have h4 : (w.im / ‖(w : ℂ)‖ ^ 2) = w.im * (‖(w : ℂ)‖ ^ 2)⁻¹ := div_eq_mul_inv _ _
  rw [Work.Kernels.scale, h1, h4]
  have h2 : w.im * (‖(w : ℂ)‖ ^ 2)⁻¹ ≤ w.im⁻¹ + ‖(w : ℂ)‖ := by
    rw [mul_inv_le_iff₀ (by positivity : (0:ℝ) < ‖(w : ℂ)‖ ^ 2)]
    have h8 : w.im⁻¹ * w.im ^ 2 = w.im := by
      field_simp
    have h7 : w.im⁻¹ * w.im ^ 2 ≤ w.im⁻¹ * ‖(w : ℂ)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    nlinarith [h7, h8, hwpos, sq_nonneg (‖(w : ℂ)‖),
      mul_nonneg (le_of_lt hpos) (sq_nonneg (‖(w : ℂ)‖))]
  linarith


/-! ## §5  The target -/

/-- **The two-regime upper bound is sharp on `E`.**

For `w ∈ E = KEpsilon` and `t ≥ scale w` the CKMRV kernel `Kaxis (Kfun ℓ d) w t` differs from
its cusp-`i∞` model `Aexp (Gcusp ℓ d) w t` by `O((scale w)^N t^M e^{-πt})`.  By the `S`-transport
of §2--§3 (with `τ = S • w ∈ 𝔽`) this is exactly the sharp funnel statement
`Khat_funnel_tail_sharp`, transported back along `Kfun(S • τ) = -τᵈᐟ² K̂(τ)` and
`𝒢(S • τ) = -τᵈᐟ² (𝒢₊(τ) - 𝒢₋(τ))/2`. -/
theorem ETailE_one (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon →
        Work.Kernels.scale w ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t‖
          ≤ C * (Work.Kernels.scale w) ^ N * t ^ M * Real.exp (-(Real.pi * t)) := by
  obtain ⟨C, N, M, hC, hN, hM, hbound⟩ := Khat_funnel_tail_sharp ℓ d hd
  rcases hd with h8 | h24
  · subst h8
    refine ⟨C * 2 ^ M * 3 ^ N, N + 4, M, by positivity, by positivity, hM, ?_⟩
    intro w t hw hwt
    have hsw : Funnel (ModularGroup.S • w) := S_smul_mem_funnel hw
    have hinter : (ModularGroup.S • w).im + 1 ≤ t :=
      le_trans (im_S_smul_add_one_le_scale w) hwt
    have ht0 : 0 < t := lt_of_lt_of_le (Work.Kernels.scale_pos w) hwt
    have ht1 : (1 : ℝ) ≤ t := le_trans (Work.Kernels.one_le_scale w) hwt
    have hspos : 0 < scale w := Work.Kernels.scale_pos w
    have hKw : Kfun ℓ 8 w (imagAxis t ht0)
        = - ((ModularGroup.S • w : ℍ) : ℂ) ^ 4 * Khat ℓ 8 (ModularGroup.S • w) (imagAxis t ht0) := by
      have h := Kfun_S_smul_eight ℓ (ModularGroup.S • w) (imagAxis t ht0)
      rwa [S_smul_S_smul] at h
    have hGw : Compact.Gfun 8 ℓ w (imagAxis t ht0)
        = - ((ModularGroup.S • w : ℍ) : ℂ) ^ 4
            * (Compact.Gplus 8 (ModularGroup.S • w) (imagAxis t ht0)
                - Compact.Gminus 8 ℓ (ModularGroup.S • w) (imagAxis t ht0)) / 2 := by
      have h := Gfun_S_smul_eight ℓ (ModularGroup.S • w) (imagAxis t ht0)
      rwa [S_smul_S_smul] at h
    have hK : Kaxis (Kfun ℓ 8) w t = Kfun ℓ 8 w (imagAxis t ht0) := by
      rw [Kaxis, dif_pos ht0]
    have hAe : Aexp (Gcusp ℓ 8) w t = Compact.Gfun 8 ℓ w (imagAxis t ht0) :=
      Aexp_Gcusp_eq_Gfun ℓ 8 w t ht0
    have hfac : Kaxis (Kfun ℓ 8) w t - Aexp (Gcusp ℓ 8) w t
        = - ((ModularGroup.S • w : ℍ) : ℂ) ^ 4
            * (Khat ℓ 8 (ModularGroup.S • w) (imagAxis t ht0)
                - (Compact.Gplus 8 (ModularGroup.S • w) (imagAxis t ht0)
                    - Compact.Gminus 8 ℓ (ModularGroup.S • w) (imagAxis t ht0)) / 2) := by
      rw [hK, hAe, hKw, hGw]; ring
    have hb := hbound (ModularGroup.S • w) (imagAxis t ht0) t hsw hinter rfl
    rw [hfac, norm_mul, norm_neg, norm_pow]
    have hnorm : ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ≤ scale w := EtailE.E_norm_S_le_scale w
    have hscaleS : scale (ModularGroup.S • w) ≤ 3 * scale w := EtailE.E_scale_S_le hw
    have hpow4 : ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ 4 ≤ (scale w) ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 4
    have hpowN : (scale (ModularGroup.S • w)) ^ N ≤ (3 * scale w) ^ N :=
      Real.rpow_le_rpow (Work.Kernels.scale_pos _).le hscaleS hN
    have h3N : (3 * scale w) ^ N = 3 ^ N * (scale w) ^ N :=
      Real.mul_rpow (by norm_num) hspos.le
    have h2M : (1 + t) ^ M ≤ 2 ^ M * t ^ M := by
      have h2t : (2 * t) ^ M = 2 ^ M * t ^ M :=
        Real.mul_rpow (by norm_num) (le_of_lt ht0)
      rw [← h2t]
      exact Real.rpow_le_rpow (by positivity) (by linarith) hM
    have hexp_nn : (0 : ℝ) ≤ Real.exp (-(Real.pi * t)) := (Real.exp_pos _).le
    have hCN : (0 : ℝ) ≤ C * (3 ^ N * (scale w) ^ N) * (2 ^ M * t ^ M) * Real.exp (-(Real.pi * t)) := by
      have h1 : (0 : ℝ) ≤ 3 ^ N := Real.rpow_nonneg (by norm_num) _
      have h2 : (0 : ℝ) ≤ (scale w) ^ N := Real.rpow_nonneg hspos.le _
      have h3 : (0 : ℝ) ≤ 2 ^ M := Real.rpow_nonneg (by norm_num) _
      have h4 : (0 : ℝ) ≤ t ^ M := Real.rpow_nonneg (le_of_lt ht0) _
      positivity
    calc ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ 4
            * ‖Khat ℓ 8 (ModularGroup.S • w) (imagAxis t ht0)
                - (Compact.Gplus 8 (ModularGroup.S • w) (imagAxis t ht0)
                    - Compact.Gminus 8 ℓ (ModularGroup.S • w) (imagAxis t ht0)) / 2‖
        ≤ (scale w) ^ 4 * (C * (scale (ModularGroup.S • w)) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * t))) :=
          mul_le_mul hpow4 hb (norm_nonneg _) (by positivity)
      _ ≤ (scale w) ^ 4 * (C * (3 ^ N * (scale w) ^ N) * (2 ^ M * t ^ M)
              * Real.exp (-(Real.pi * t))) := by
          have he_nn : (0 : ℝ) ≤ Real.exp (-(Real.pi * t)) := (Real.exp_pos _).le
          have h2M_nn : (0 : ℝ) ≤ 2 ^ M * t ^ M :=
            mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (le_of_lt ht0) _)
          have h3N_nn : (0 : ℝ) ≤ 3 ^ N * (scale w) ^ N :=
            mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hspos.le _)
          have hA : C * (scale (ModularGroup.S • w)) ^ N ≤ C * (3 ^ N * (scale w) ^ N) :=
            mul_le_mul_of_nonneg_left (h3N ▸ hpowN) hC.le
          have h1 : C * (scale (ModularGroup.S • w)) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t))
              ≤ C * (3 ^ N * (scale w) ^ N) * (2 ^ M * t ^ M) * Real.exp (-(Real.pi * t)) := by
            calc C * (scale (ModularGroup.S • w)) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t))
                = (C * (scale (ModularGroup.S • w)) ^ N)
                    * ((1 + t) ^ M * Real.exp (-(Real.pi * t))) := by ring
              _ ≤ (C * (3 ^ N * (scale w) ^ N))
                    * ((2 ^ M * t ^ M) * Real.exp (-(Real.pi * t))) := by
                  refine mul_le_mul hA (mul_le_mul_of_nonneg_right h2M he_nn) ?_ ?_
                  · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) he_nn
                  · exact mul_nonneg hC.le h3N_nn
              _ = C * (3 ^ N * (scale w) ^ N) * (2 ^ M * t ^ M)
                    * Real.exp (-(Real.pi * t)) := by ring
          exact mul_le_mul_of_nonneg_left h1 (pow_nonneg hspos.le 4)
      _ = C * 2 ^ M * 3 ^ N * (scale w) ^ (N + 4) * t ^ M * Real.exp (-(Real.pi * t)) := by
          rw [show (scale w) ^ 4 = (scale w) ^ ((4 : ℝ)) from (Real.rpow_natCast _ 4).symm,
              Real.rpow_add hspos]
          ring
  · subst h24
    refine ⟨C * 2 ^ M * 3 ^ N, N + 12, M, by positivity, by positivity, hM, ?_⟩
    intro w t hw hwt
    have hsw : Funnel (ModularGroup.S • w) := S_smul_mem_funnel hw
    have hinter : (ModularGroup.S • w).im + 1 ≤ t :=
      le_trans (im_S_smul_add_one_le_scale w) hwt
    have ht0 : 0 < t := lt_of_lt_of_le (Work.Kernels.scale_pos w) hwt
    have ht1 : (1 : ℝ) ≤ t := le_trans (Work.Kernels.one_le_scale w) hwt
    have hspos : 0 < scale w := Work.Kernels.scale_pos w
    have hKw : Kfun ℓ 24 w (imagAxis t ht0)
        = - ((ModularGroup.S • w : ℍ) : ℂ) ^ 12 * Khat ℓ 24 (ModularGroup.S • w) (imagAxis t ht0) := by
      have h := Kfun_S_smul_twentyfour ℓ (ModularGroup.S • w) (imagAxis t ht0)
      rwa [S_smul_S_smul] at h
    have hGw : Compact.Gfun 24 ℓ w (imagAxis t ht0)
        = - ((ModularGroup.S • w : ℍ) : ℂ) ^ 12
            * (Compact.Gplus 24 (ModularGroup.S • w) (imagAxis t ht0)
                - Compact.Gminus 24 ℓ (ModularGroup.S • w) (imagAxis t ht0)) / 2 := by
      have h := Gfun_S_smul_twentyfour ℓ (ModularGroup.S • w) (imagAxis t ht0)
      rwa [S_smul_S_smul] at h
    have hK : Kaxis (Kfun ℓ 24) w t = Kfun ℓ 24 w (imagAxis t ht0) := by
      rw [Kaxis, dif_pos ht0]
    have hAe : Aexp (Gcusp ℓ 24) w t = Compact.Gfun 24 ℓ w (imagAxis t ht0) :=
      Aexp_Gcusp_eq_Gfun ℓ 24 w t ht0
    have hfac : Kaxis (Kfun ℓ 24) w t - Aexp (Gcusp ℓ 24) w t
        = - ((ModularGroup.S • w : ℍ) : ℂ) ^ 12
            * (Khat ℓ 24 (ModularGroup.S • w) (imagAxis t ht0)
                - (Compact.Gplus 24 (ModularGroup.S • w) (imagAxis t ht0)
                    - Compact.Gminus 24 ℓ (ModularGroup.S • w) (imagAxis t ht0)) / 2) := by
      rw [hK, hAe, hKw, hGw]; ring
    have hb := hbound (ModularGroup.S • w) (imagAxis t ht0) t hsw hinter rfl
    rw [hfac, norm_mul, norm_neg, norm_pow]
    have hnorm : ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ≤ scale w := EtailE.E_norm_S_le_scale w
    have hscaleS : scale (ModularGroup.S • w) ≤ 3 * scale w := EtailE.E_scale_S_le hw
    have hpow : ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ 12 ≤ (scale w) ^ 12 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 12
    have hpowN : (scale (ModularGroup.S • w)) ^ N ≤ (3 * scale w) ^ N :=
      Real.rpow_le_rpow (Work.Kernels.scale_pos _).le hscaleS hN
    have h3N : (3 * scale w) ^ N = 3 ^ N * (scale w) ^ N :=
      Real.mul_rpow (by norm_num) hspos.le
    have h2M : (1 + t) ^ M ≤ 2 ^ M * t ^ M := by
      have h2t : (2 * t) ^ M = 2 ^ M * t ^ M :=
        Real.mul_rpow (by norm_num) (le_of_lt ht0)
      rw [← h2t]
      exact Real.rpow_le_rpow (by positivity) (by linarith) hM
    calc ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ 12
            * ‖Khat ℓ 24 (ModularGroup.S • w) (imagAxis t ht0)
                - (Compact.Gplus 24 (ModularGroup.S • w) (imagAxis t ht0)
                    - Compact.Gminus 24 ℓ (ModularGroup.S • w) (imagAxis t ht0)) / 2‖
        ≤ (scale w) ^ 12 * (C * (scale (ModularGroup.S • w)) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * t))) :=
          mul_le_mul hpow hb (norm_nonneg _) (by positivity)
      _ ≤ (scale w) ^ 12 * (C * (3 ^ N * (scale w) ^ N) * (2 ^ M * t ^ M)
              * Real.exp (-(Real.pi * t))) := by
          have he_nn : (0 : ℝ) ≤ Real.exp (-(Real.pi * t)) := (Real.exp_pos _).le
          have h2M_nn : (0 : ℝ) ≤ 2 ^ M * t ^ M :=
            mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (le_of_lt ht0) _)
          have h3N_nn : (0 : ℝ) ≤ 3 ^ N * (scale w) ^ N :=
            mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hspos.le _)
          have hA : C * (scale (ModularGroup.S • w)) ^ N ≤ C * (3 ^ N * (scale w) ^ N) :=
            mul_le_mul_of_nonneg_left (h3N ▸ hpowN) hC.le
          have h1 : C * (scale (ModularGroup.S • w)) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t))
              ≤ C * (3 ^ N * (scale w) ^ N) * (2 ^ M * t ^ M) * Real.exp (-(Real.pi * t)) := by
            calc C * (scale (ModularGroup.S • w)) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * t))
                = (C * (scale (ModularGroup.S • w)) ^ N)
                    * ((1 + t) ^ M * Real.exp (-(Real.pi * t))) := by ring
              _ ≤ (C * (3 ^ N * (scale w) ^ N))
                    * ((2 ^ M * t ^ M) * Real.exp (-(Real.pi * t))) := by
                  refine mul_le_mul hA (mul_le_mul_of_nonneg_right h2M he_nn) ?_ ?_
                  · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) he_nn
                  · exact mul_nonneg hC.le h3N_nn
              _ = C * (3 ^ N * (scale w) ^ N) * (2 ^ M * t ^ M)
                    * Real.exp (-(Real.pi * t)) := by ring
          exact mul_le_mul_of_nonneg_left h1 (pow_nonneg hspos.le 12)
      _ = C * 2 ^ M * 3 ^ N * (scale w) ^ (N + 12) * t ^ M * Real.exp (-(Real.pi * t)) := by
          rw [show (scale w) ^ 12 = (scale w) ^ ((12 : ℝ)) from (Real.rpow_natCast _ 12).symm,
              Real.rpow_add hspos]
          ring

end Work.Asymptotics

end
