import Mathlib
import Submission.Work.Asymptotics.arcRegion
import Submission.Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded
import Submission.Work.Asymptotics.KaxisMid.norm_le_of_norm_le_of_two_zeros
import Submission.Work.Residues.ResidueOrbit
import Submission.Work.Residues.Poles
import Submission.Work.Residues.phiPlus_crossed_translates_eq_zero
import Submission.Work.Asymptotics.orbit_imagAxis_of_mem_DomainD
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis
import Submission.Work.Kernels.ClearLink.KPlusClear_eq_smul
import Submission.Work.Kernels.ClearLink.KMinusClear_eq_smul
import Submission.Work.Asymptotics.Graze.KeyBound
import Submission.Work.Asymptotics.KaxisMid.LocalMiddle

set_option maxHeartbeats 3200000

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups UpperHalfPlane Topology

namespace Work.Asymptotics
/-- The set of closed conditions holding on the closure of `arcT`. -/
def arcCl : Set ℍ :=
  {τ | -1 ≤ τ.re ∧ τ.re ≤ 1 ∧ (1:ℝ)/2 ≤ ‖(τ:ℂ) - (1/2:ℂ)‖ ∧
    (1:ℝ)/2 ≤ ‖(τ:ℂ) + (1/2:ℂ)‖ ∧
    (‖(τ:ℂ) - (1/2:ℂ)‖ ≤ 1/2 + 1/10 ∨ ‖(τ:ℂ) + (1/2:ℂ)‖ ≤ 1/2 + 1/10) ∧
    (1:ℝ)/2 ≤ (ModularGroup.S • τ).im ∧ (ModularGroup.S • τ).im ≤ 2}

lemma closure_arcT_subset_arcCl : closure arcT ⊆ arcCl := by
  intro τ hτ
  have hc : Continuous (fun w : ℍ => (ModularGroup.S • w).im) :=
    UpperHalfPlane.continuous_im.comp (continuous_const.smul continuous_id)
  have hd1 : IsClosed {w : ℍ | -1 ≤ w.re} := isClosed_le continuous_const UpperHalfPlane.continuous_re
  have hd2 : IsClosed {w : ℍ | w.re ≤ 1} := isClosed_le UpperHalfPlane.continuous_re continuous_const
  have hd3 : IsClosed {w : ℍ | (1:ℝ)/2 ≤ ‖(w:ℂ) - (1/2:ℂ)‖} :=
    isClosed_le continuous_const ((continuous_coe.sub continuous_const).norm)
  have hd4 : IsClosed {w : ℍ | (1:ℝ)/2 ≤ ‖(w:ℂ) + (1/2:ℂ)‖} :=
    isClosed_le continuous_const ((continuous_coe.add continuous_const).norm)
  have hd5 : IsClosed {w : ℍ | ‖(w:ℂ) - (1/2:ℂ)‖ ≤ 1/2 + 1/10 ∨ ‖(w:ℂ) + (1/2:ℂ)‖ ≤ 1/2 + 1/10} :=
    (isClosed_le ((continuous_coe.sub continuous_const).norm) continuous_const).union
      (isClosed_le ((continuous_coe.add continuous_const).norm) continuous_const)
  have hd6 : IsClosed {w : ℍ | (1:ℝ)/2 ≤ (ModularGroup.S • w).im} := isClosed_le continuous_const hc
  have hd7 : IsClosed {w : ℍ | (ModularGroup.S • w).im ≤ 2} := isClosed_le hc continuous_const
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact closure_minimal (fun w hw => le_of_lt hw.1.1) hd1 hτ
  · exact closure_minimal (fun w hw => le_of_lt hw.1.2.1) hd2 hτ
  · exact closure_minimal (fun w hw => le_of_lt hw.1.2.2.1) hd3 hτ
  · exact closure_minimal (fun w hw => le_of_lt hw.1.2.2.2) hd4 hτ
  · exact closure_minimal (fun w hw => hw.2.2.2.elim (fun h => Or.inl (le_of_lt h))
      (fun h => Or.inr (le_of_lt h))) hd5 hτ
  · exact closure_minimal (fun w hw => hw.2.1) hd6 hτ
  · exact closure_minimal (fun w hw => hw.2.2.1) hd7 hτ

/-- Squared distance form. -/
lemma arcCl_normSq_sub {τ : ℍ} : ‖(τ:ℂ) - (1/2:ℂ)‖^2 = τ.re^2 - τ.re + τ.im^2 + 1/4 := by
  have h : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) := by norm_num
  rw [h, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

lemma arcCl_normSq_add {τ : ℍ} : ‖(τ:ℂ) + (1/2:ℂ)‖^2 = τ.re^2 + τ.re + τ.im^2 + 1/4 := by
  have h : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) := by norm_num
  rw [h, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- A point of the closure of `arcT` has nonzero real part. -/
lemma arcCl_re_ne_zero {τ : ℍ} (hτ : τ ∈ arcCl) : τ.re ≠ 0 := by
  intro h0
  obtain ⟨-, -, -, -, harc, hlo, hhi⟩ := hτ
  have hypos : 0 < τ.im := τ.im_pos
  have hnsq : Complex.normSq (τ : ℂ) = τ.im^2 := by
    rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, h0]
    ring
  have himS : (ModularGroup.S • τ).im = τ.im / Complex.normSq (τ : ℂ) := by
    rw [← UpperHalfPlane.coe_im, UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk,
      Complex.inv_im, Complex.neg_im, Complex.normSq_neg, UpperHalfPlane.coe_im]
    ring
  have himS' : (ModularGroup.S • τ).im = 1 / τ.im := by
    rw [himS, hnsq]
    have hne : (τ.im : ℂ) ≠ 0 := by simpa using hypos.ne'
    field_simp
  have hsq : ‖(τ:ℂ) - (1/2:ℂ)‖^2 = τ.im^2 + 1/4 := by
    rw [arcCl_normSq_sub, h0]; ring
  have hle : τ.im^2 ≤ 11/100 := by
    have h2 : ‖(τ:ℂ) - (1/2:ℂ)‖ ≤ 6/10 := by
      rcases harc with h | h
      · linarith [h]
      · have : ‖(τ:ℂ) + (1/2:ℂ)‖^2 = τ.im^2 + 1/4 := by rw [arcCl_normSq_add, h0]; ring
        nlinarith [norm_nonneg ((τ:ℂ) + (1/2:ℂ)), h, this]
    nlinarith [norm_nonneg ((τ:ℂ) - (1/2:ℂ)), h2, hsq]
  have hge : 1/2 ≤ τ.im := by
    rw [himS'] at hhi
    have h2 : 1 / τ.im ≤ 2 := hhi
    rw [div_le_iff₀ hypos] at h2
    linarith
  nlinarith [hle, hge]
/-- The two real equations `β = uσ - vρt`, `αt = uρt + vσ` for `γ • (it) = τ`. -/
lemma entries_of_smul_imagAxis' {γ : SL(2,ℤ)} {t : ℝ} (ht : 0 < t) (τ : ℍ)
    (h : γ • Work.Kernels.imagAxis t ht = τ) :
    ((γ 0 1 : ℤ) : ℝ) = τ.re * (γ 1 1 : ℤ) - τ.im * (γ 1 0 : ℤ) * t ∧
    ((γ 0 0 : ℤ) : ℝ) * t = τ.re * (γ 1 0 : ℤ) * t + τ.im * (γ 1 1 : ℤ) := by
  have hcoe : ((γ • Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (τ : ℂ) := by rw [h]
  rw [UpperHalfPlane.coe_specialLinearGroup_apply] at hcoe
  simp only [Work.Kernels.imagAxis, UpperHalfPlane.coe_mk] at hcoe
  have hcast : ∀ m : ℤ, ((algebraMap ℤ ℝ m : ℂ)) = (m : ℂ) := fun m => by simp
  simp only [hcast] at hcoe
  have hden : ((γ 1 0 : ℤ) : ℂ) * ((t : ℂ) * Complex.I) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
      mul_zero, sub_zero, zero_mul, add_zero, mul_one] at hre him
    have h11 : γ 1 1 = 0 := by
      have hh : ((γ 1 1 : ℤ) : ℝ) = 0 := by simpa using hre
      exact_mod_cast hh
    have h10 : γ 1 0 = 0 := by
      have ht0 : (t : ℝ) ≠ 0 := ne_of_gt ht
      have hh : ((γ 1 0 : ℤ) : ℝ) * t = 0 := by simpa using him
      have : ((γ 1 0 : ℤ) : ℝ) = 0 := (mul_eq_zero.mp hh).resolve_right ht0
      exact_mod_cast this
    have hdet := γ.2
    rw [Matrix.det_fin_two] at hdet
    rw [h10, h11] at hdet
    norm_num at hdet
  have hmain : ((γ 0 0 : ℤ) : ℂ) * ((t : ℂ) * Complex.I) + ((γ 0 1 : ℤ) : ℂ)
      = (τ : ℂ) * (((γ 1 0 : ℤ) : ℂ) * ((t : ℂ) * Complex.I) + ((γ 1 1 : ℤ) : ℂ)) :=
    (div_eq_iff hden).mp hcoe
  have hcoeτ : (τ : ℂ) = (τ.re : ℂ) + (τ.im : ℂ) * Complex.I := by
    have hh := Complex.re_add_im (τ : ℂ)
    rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hh
    exact hh.symm
  rw [hcoeτ] at hmain
  constructor
  · have hre := congrArg Complex.re hmain
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
      mul_zero, sub_zero, zero_mul, add_zero, mul_one] at hre
    have h' : ((γ 0 1 : ℤ) : ℝ) = τ.re * (γ 1 1 : ℤ) - τ.im * (γ 1 0 : ℤ) * t := by

      linarith [hre]
    exact h'
  · have him := congrArg Complex.im hmain
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
      mul_zero, sub_zero, zero_mul, add_zero, mul_one] at him
    have h' : ((γ 0 0 : ℤ) : ℝ) * t = τ.re * (γ 1 0 : ℤ) * t + τ.im * (γ 1 1 : ℤ) := by

      linarith [him]
    exact h'

/-- The key identities. -/
lemma key_identities {γ : SL(2,ℤ)} {t : ℝ} (ht : 0 < t) {τ : ℍ}
    (hR : ((γ 0 1 : ℤ) : ℝ) = τ.re * (γ 1 1 : ℤ) - τ.im * (γ 1 0 : ℤ) * t)
    (hI : ((γ 0 0 : ℤ) : ℝ) * t = τ.re * (γ 1 0 : ℤ) * t + τ.im * (γ 1 1 : ℤ))
    (hdet : (γ 0 0 : ℤ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1) :
    ((γ 0 0 : ℤ) : ℝ)^2 * t^2 + ((γ 0 1 : ℤ) : ℝ)^2
      = (τ.re^2 + τ.im^2) * (((γ 1 0 : ℤ) : ℝ)^2 * t^2 + ((γ 1 1 : ℤ) : ℝ)^2) ∧
    ((γ 0 0 : ℤ) : ℝ) * (γ 1 0 : ℤ) * t^2 + ((γ 0 1 : ℤ) : ℝ) * (γ 1 1 : ℤ)
      = τ.re * (((γ 1 0 : ℤ) : ℝ)^2 * t^2 + ((γ 1 1 : ℤ) : ℝ)^2) ∧
    t = τ.im * (((γ 1 0 : ℤ) : ℝ)^2 * t^2 + ((γ 1 1 : ℤ) : ℝ)^2) := by
  have hdetR : ((γ 0 0 : ℤ) : ℝ) * (γ 1 1 : ℤ) - ((γ 0 1 : ℤ) : ℝ) * (γ 1 0 : ℤ) = 1 := by
    exact_mod_cast hdet
  refine ⟨?_, ?_, ?_⟩
  · have h2 : (((γ 0 0 : ℤ) : ℝ) * t)^2 + ((γ 0 1 : ℤ) : ℝ)^2
        = (τ.re * (γ 1 0 : ℤ) * t + τ.im * (γ 1 1 : ℤ))^2
          + (τ.re * (γ 1 1 : ℤ) - τ.im * (γ 1 0 : ℤ) * t)^2 := by
      rw [← hI, ← hR]
    calc ((γ 0 0 : ℤ) : ℝ)^2 * t^2 + ((γ 0 1 : ℤ) : ℝ)^2
        = (((γ 0 0 : ℤ) : ℝ) * t)^2 + ((γ 0 1 : ℤ) : ℝ)^2 := by ring
      _ = (τ.re * (γ 1 0 : ℤ) * t + τ.im * (γ 1 1 : ℤ))^2
            + (τ.re * (γ 1 1 : ℤ) - τ.im * (γ 1 0 : ℤ) * t)^2 := h2
      _ = (τ.re^2 + τ.im^2) * (((γ 1 0 : ℤ) : ℝ)^2 * t^2 + ((γ 1 1 : ℤ) : ℝ)^2) := by ring
  · have h2 : (((γ 0 0 : ℤ) : ℝ) * t) * ((γ 1 0 : ℤ) * t) + ((γ 0 1 : ℤ) : ℝ) * (γ 1 1 : ℤ)
        = (τ.re * (γ 1 0 : ℤ) * t + τ.im * (γ 1 1 : ℤ)) * ((γ 1 0 : ℤ) * t)
          + (τ.re * (γ 1 1 : ℤ) - τ.im * (γ 1 0 : ℤ) * t) * (γ 1 1 : ℤ) := by
      rw [← hI, ← hR]
    calc ((γ 0 0 : ℤ) : ℝ) * (γ 1 0 : ℤ) * t^2 + ((γ 0 1 : ℤ) : ℝ) * (γ 1 1 : ℤ)
        = (((γ 0 0 : ℤ) : ℝ) * t) * ((γ 1 0 : ℤ) * t)
          + ((γ 0 1 : ℤ) : ℝ) * (γ 1 1 : ℤ) := by ring
      _ = (τ.re * (γ 1 0 : ℤ) * t + τ.im * (γ 1 1 : ℤ)) * ((γ 1 0 : ℤ) * t)
          + (τ.re * (γ 1 1 : ℤ) - τ.im * (γ 1 0 : ℤ) * t) * (γ 1 1 : ℤ) := h2
      _ = τ.re * (((γ 1 0 : ℤ) : ℝ)^2 * t^2 + ((γ 1 1 : ℤ) : ℝ)^2) := by ring
  · have h4 : ((γ 0 0 : ℤ) : ℝ) * t * (γ 1 1 : ℤ) - ((γ 0 1 : ℤ) : ℝ) * (γ 1 0 : ℤ) * t = t := by
      nlinarith [hdetR]
    have h5 : ((γ 0 0 : ℤ) : ℝ) * t * (γ 1 1 : ℤ) - ((γ 0 1 : ℤ) : ℝ) * (γ 1 0 : ℤ) * t
        = τ.im * (((γ 1 0 : ℤ) : ℝ)^2 * t^2 + ((γ 1 1 : ℤ) : ℝ)^2) := by
      have h2 : ((γ 0 0 : ℤ) : ℝ) * t * (γ 1 1 : ℤ) - ((γ 0 1 : ℤ) : ℝ) * (γ 1 0 : ℤ) * t
          = (τ.re * (γ 1 0 : ℤ) * t + τ.im * (γ 1 1 : ℤ)) * (γ 1 1 : ℤ)
            - (τ.re * (γ 1 1 : ℤ) - τ.im * (γ 1 0 : ℤ) * t) * ((γ 1 0 : ℤ) * t) := by
        rw [← hI, ← hR]; ring
      rw [h2]; ring
    linarith [h4, h5]

end Work.Asymptotics

namespace Work.Asymptotics

/-- The `a ≠ 0`, `b ≠ 0` cases are impossible. -/
private lemma entries_contra {a b c d : ℤ} {t As Ds : ℝ} (ht : 0 < t)
    (hb : b ≠ 0) (ha : a ≠ 0)
    (hAs : As = (a:ℝ)^2*t^2 + (b:ℝ)^2) (hAs_pos : 0 < As)
    (hle : As ≤ 2*t) (hquad : As*(Ds-As) = t^2)
    (hDs : Ds = (c:ℝ)^2*t^2 + (d:ℝ)^2) : False := by
  have hb1 : (1:ℝ) ≤ (b:ℝ)^2 := by
    have hbz : 1 ≤ b^2 := by
      have : b ≤ -1 ∨ 1 ≤ b := by omega
      rcases this with h | h <;> nlinarith [h]
    have : (((b^2 : ℤ)) : ℝ) ≥ 1 := by exact_mod_cast hbz
    simpa using this
  have hle' : (a:ℝ)^2*t^2 + (b:ℝ)^2 ≤ 2*t := by rw [hAs] at hle; exact hle
  have hAge1 : (1:ℝ) ≤ As := by rw [hAs]; linarith [sq_nonneg ((a:ℝ)*t), hb1]
  have htge : (1:ℝ)/2 ≤ t := by linarith
  have ha2le : (a:ℝ)^2 ≤ 4 := by
    have h1 : (a:ℝ)^2 * t^2 ≤ 2*t := by linarith [hle', sq_nonneg (b:ℝ)]
    have h2 : (a:ℝ)^2 * t ≤ 2 := by nlinarith [h1, ht]
    nlinarith [h2, ht, htge]
  have ha_le : (a:ℝ) ≤ 2 := by nlinarith [sq_nonneg ((a:ℝ)-2), ha2le]
  have ha_ge : (-2:ℝ) ≤ (a:ℝ) := by nlinarith [sq_nonneg ((a:ℝ)+2), ha2le]
  have ha2Zle : a ≤ 2 := by exact_mod_cast ha_le
  have ha2Zge : -2 ≤ a := by exact_mod_cast ha_ge
  have ha_int : a = -2 ∨ a = -1 ∨ a = 1 ∨ a = 2 := by omega
  rcases ha_int with ha1 | ha1 | ha1 | ha1
  · have hAs2 : As = 4*t^2 + (b:ℝ)^2 := by rw [hAs, ha1]; first | rfl | (push_cast; ring)
    have h4 : (4:ℝ)*t^2 - 2*t + 1 ≤ 0 := by nlinarith [hle', hAs2, hb1]
    nlinarith [h4, sq_nonneg (2*t - 1/2)]
  · -- a = -1
    have hAs2 : As = t^2 + (b:ℝ)^2 := by rw [hAs, ha1]; first | rfl | (push_cast; ring)
    have hb1' : (b:ℝ)^2 = 1 := by
      have hle1 : (b:ℝ)^2 ≤ 1 := by nlinarith [hle', hAs2, sq_nonneg (t-1)]
      linarith
    have ht1 : t = 1 := by
      have h4 : t^2 - 2*t + 1 ≤ 0 := by nlinarith [hle', hAs2, hb1']
      nlinarith [h4, sq_nonneg (t-1)]
    have hA2 : As = 2 := by rw [hAs2, ht1, hb1']; norm_num
    have hDs52 : Ds = 5/2 := by
      have h := hquad; rw [hA2, ht1] at h; linarith
    rw [hDs, ht1] at hDs52; norm_num at hDs52
    have hInt : ∃ n : ℤ, (c:ℝ)^2 + (d:ℝ)^2 = (n:ℝ) := ⟨c^2+d^2, by push_cast; ring⟩
    obtain ⟨n, hn⟩ := hInt
    rw [hn] at hDs52
    have h2n : (5:ℤ) = 2*n := by
      have : (5:ℝ) = 2*(n:ℝ) := by linarith
      exact_mod_cast this
    omega
  · -- a = 1
    have hAs2 : As = t^2 + (b:ℝ)^2 := by rw [hAs, ha1]; first | rfl | (push_cast; ring)
    have hb1' : (b:ℝ)^2 = 1 := by
      have hle1 : (b:ℝ)^2 ≤ 1 := by nlinarith [hle', hAs2, sq_nonneg (t-1)]
      linarith
    have ht1 : t = 1 := by
      have h4 : t^2 - 2*t + 1 ≤ 0 := by nlinarith [hle', hAs2, hb1']
      nlinarith [h4, sq_nonneg (t-1)]
    have hA2 : As = 2 := by rw [hAs2, ht1, hb1']; norm_num
    have hDs52 : Ds = 5/2 := by
      have h := hquad; rw [hA2, ht1] at h; linarith
    rw [hDs, ht1] at hDs52; norm_num at hDs52
    have hInt : ∃ n : ℤ, (c:ℝ)^2 + (d:ℝ)^2 = (n:ℝ) := ⟨c^2+d^2, by push_cast; ring⟩
    obtain ⟨n, hn⟩ := hInt
    rw [hn] at hDs52
    have h2n : (5:ℤ) = 2*n := by
      have : (5:ℝ) = 2*(n:ℝ) := by linarith
      exact_mod_cast this
    omega
  · have hAs2 : As = 4*t^2 + (b:ℝ)^2 := by rw [hAs, ha1]; first | rfl | (push_cast; ring)
    have h4 : (4:ℝ)*t^2 - 2*t + 1 ≤ 0 := by nlinarith [hle', hAs2, hb1]
    nlinarith [h4, sq_nonneg (2*t - 1/2)]

end Work.Asymptotics

namespace Work.Asymptotics

/-- The set of `8` entry patterns. -/
def isGraze (a b c d : ℤ) : Prop :=
  (a = 1 ∧ b = 0 ∧ c = 1 ∧ d = 1) ∨ (a = -1 ∧ b = 0 ∧ c = -1 ∧ d = -1) ∨
  (a = 0 ∧ b = 1 ∧ c = -1 ∧ d = 1) ∨ (a = 0 ∧ b = -1 ∧ c = 1 ∧ d = -1) ∨
  (a = 1 ∧ b = 0 ∧ c = -1 ∧ d = 1) ∨ (a = -1 ∧ b = 0 ∧ c = 1 ∧ d = -1) ∨
  (a = 0 ∧ b = 1 ∧ c = -1 ∧ d = -1) ∨ (a = 0 ∧ b = -1 ∧ c = 1 ∧ d = 1)

set_option maxHeartbeats 3200000 in
/-- **The entry-level classification.** -/
lemma entries_classification {a b c d : ℤ} {t u v : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1)
    (hA : (a:ℝ)^2*t^2 + (b:ℝ)^2 = (u^2+v^2)*((c:ℝ)^2*t^2 + (d:ℝ)^2))
    (hB : (a:ℝ)*(c:ℝ)*t^2 + (b:ℝ)*(d:ℝ) = u*((c:ℝ)^2*t^2 + (d:ℝ)^2))
    (hIm : t = v*((c:ℝ)^2*t^2 + (d:ℝ)^2))
    (hvp : 0 < v)
    (hdet : a*d - b*c = 1)
    (harc : ((a:ℝ)^2*t^2 + (b:ℝ)^2 = (a:ℝ)*(c:ℝ)*t^2 + (b:ℝ)*(d:ℝ)) ∨
            ((a:ℝ)^2*t^2 + (b:ℝ)^2 = -((a:ℝ)*(c:ℝ)*t^2 + (b:ℝ)*(d:ℝ))))
    (hImS : (1:ℝ)/2 ≤ t/((a:ℝ)^2*t^2 + (b:ℝ)^2) ∧
            t/((a:ℝ)^2*t^2 + (b:ℝ)^2) ≤ 2) :
    isGraze a b c d := by
  have hDpos : 0 < (c:ℝ)^2*t^2 + (d:ℝ)^2 := by nlinarith [hIm, ht, hvp]
  set Ds : ℝ := (c:ℝ)^2*t^2 + (d:ℝ)^2 with hDs
  set As : ℝ := (a:ℝ)^2*t^2 + (b:ℝ)^2 with hAs
  set Bs : ℝ := (a:ℝ)*(c:ℝ)*t^2 + (b:ℝ)*(d:ℝ) with hBs
  have hDpos' : 0 < Ds := hDs ▸ hDpos
  have hAs_eq : As = (u^2+v^2)*Ds := by rw [hAs, hDs]; exact hA
  have hBs_eq : Bs = u*Ds := by rw [hBs, hDs]; exact hB
  have hIm_eq : t = v*Ds := by rw [hDs]; exact hIm
  have hdet2 : As*Ds - Bs^2 = t^2 := by
    rw [hAs_eq, hBs_eq]; nlinarith [hIm_eq]
  have hquad : As*(Ds-As) = t^2 := by
    rcases harc with h | h
    · have h1 : As = Bs := by rw [hAs, hBs]; exact h
      rw [h1] at hdet2 ⊢
      nlinarith [hdet2]
    · have h1 : As = -Bs := by rw [hAs, hBs]; exact h
      rw [h1] at hdet2 ⊢
      nlinarith [hdet2]
  have hAs_pos : 0 < As := by rw [hAs_eq]; nlinarith [hDpos', sq_nonneg u, hvp]
  have hlo : t/2 ≤ As := by
    have h := hImS.2; rw [hAs] at h; rw [div_le_iff₀ hAs_pos] at h; linarith
  have hle : As ≤ 2*t := by
    have h := hImS.1; rw [hAs] at h; rw [le_div_iff₀ hAs_pos] at h; linarith
  have hb2 : (b:ℝ)^2 ≤ 2 := by
    have h1 : (b:ℝ)^2 ≤ As := by rw [hAs]; nlinarith [sq_nonneg ((a:ℝ)*t)]
    nlinarith [h1, hle, ht1]
  have hb_int : b = -1 ∨ b = 0 ∨ b = 1 := by
    have hb2Z : b^2 ≤ 2 := by
      have : ((b^2 : ℤ) : ℝ) ≤ 2 := by push_cast; linarith
      exact_mod_cast this
    have h1 : -1 ≤ b := by
      by_contra h
      have h2 : b ≤ -2 := by omega
      have h3 : (4:ℤ) ≤ b^2 := by nlinarith
      omega
    have h2 : b ≤ 1 := by
      by_contra h
      have h3 : 2 ≤ b := by omega
      have h4 : (4:ℤ) ≤ b^2 := by nlinarith
      omega
    omega
  rcases hb_int with hb | hb | hb
  · -- b = -1
    by_cases ha0 : a = 0
    · have hdet' : c = 1 := by rw [ha0, hb] at hdet; simpa using hdet
      have hAs1 : As = (b:ℝ)^2 := by rw [hAs, ha0, hb]; first | rfl | (push_cast; ring)
      have hBs1 : Bs = -(d:ℝ) := by rw [hBs, ha0, hb]; first | rfl | (push_cast; ring)
      rcases harc with h | h
      · have h2 : (d:ℝ) = -1 := by rw [hAs1, hBs1, hb] at h; norm_num at h; linarith [h]
        have hd1 : d = -1 := by exact_mod_cast h2
        refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
        simp [ha0, hb, hdet', hd1]
      · have h2 : (d:ℝ) = 1 := by rw [hAs1, hBs1, hb] at h; norm_num at h; linarith [h]
        have hd1 : d = 1 := by exact_mod_cast h2
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))
        simp [ha0, hb, hdet', hd1]
    · exact (entries_contra (a := a) (b := b) (c := c) (d := d) (t := t)
        (As := As) (Ds := Ds) ht (by rw [hb]; norm_num) ha0 hAs hAs_pos hle hquad hDs).elim
  · -- b = 0
    have hdet' : a*d = 1 := by rw [hb] at hdet; simpa using hdet
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet' with ⟨ha, hd⟩ | ⟨ha, hd⟩
    · have hAs1 : As = t^2 := by rw [hAs, ha, hb]; first | rfl | (push_cast; ring)
      have hBs1 : Bs = (c:ℝ)*t^2 := by rw [hBs, ha, hb]; first | rfl | (push_cast; ring)
      rcases harc with h | h
      · have h2 : (c:ℝ)*t^2 = t^2 := by rw [hAs1, hBs1] at h; exact h.symm
        have hc : c = 1 := by
          have h3 : (c:ℝ)*t^2 = (1:ℝ)*t^2 := by simpa using h2
          have := mul_right_cancel₀ (pow_ne_zero 2 (ne_of_gt ht)) h3
          exact_mod_cast this
        exact Or.inl (by simp [ha, hb, hc, hd])
      · have h2 : (c:ℝ)*t^2 = -(t^2) := by rw [hAs1, hBs1] at h; linarith [h]
        have hc : c = -1 := by
          have h3 : (c:ℝ)*t^2 = (-1:ℝ)*t^2 := by push_cast; linarith
          have := mul_right_cancel₀ (pow_ne_zero 2 (ne_of_gt ht)) h3
          exact_mod_cast this
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
        simp [ha, hb, hc, hd]
    · have hAs1 : As = t^2 := by rw [hAs, ha, hb]; first | rfl | (push_cast; ring)
      have hBs1 : Bs = -(c:ℝ)*t^2 := by rw [hBs, ha, hb]; first | rfl | (push_cast; ring)
      rcases harc with h | h
      · have h2 : (c:ℝ)*t^2 = -(t^2) := by rw [hAs1, hBs1] at h; linarith [h]
        have hc : c = -1 := by
          have h3 : (c:ℝ)*t^2 = (-1:ℝ)*t^2 := by push_cast; linarith
          have := mul_right_cancel₀ (pow_ne_zero 2 (ne_of_gt ht)) h3
          exact_mod_cast this
        refine Or.inr (Or.inl ?_)
        simp [ha, hb, hc, hd]
      · have h2 : (c:ℝ)*t^2 = t^2 := by rw [hAs1, hBs1] at h; linarith [h]
        have hc : c = 1 := by
          have h3 : (c:ℝ)*t^2 = (1:ℝ)*t^2 := by push_cast; linarith
          have := mul_right_cancel₀ (pow_ne_zero 2 (ne_of_gt ht)) h3
          exact_mod_cast this
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
        simp [ha, hb, hc, hd]
  · -- b = 1
    by_cases ha0 : a = 0
    · have hdet' : -c = 1 := by rw [ha0, hb] at hdet; simpa using hdet
      have hc : c = -1 := by omega
      have hAs1 : As = (b:ℝ)^2 := by rw [hAs, ha0, hb]; first | rfl | (push_cast; ring)
      have hBs1 : Bs = (d:ℝ) := by rw [hBs, ha0, hb]; first | rfl | (push_cast; ring)
      rcases harc with h | h
      · have h2 : (d:ℝ) = 1 := by rw [hAs1, hBs1, hb] at h; norm_num at h; linarith [h]
        have hd1 : d = 1 := by exact_mod_cast h2
        refine Or.inr (Or.inr (Or.inl ?_))
        simp [ha0, hb, hc, hd1]
      · have h2 : (d:ℝ) = -1 := by rw [hAs1, hBs1, hb] at h; norm_num at h; linarith [h]
        have hd1 : d = -1 := by exact_mod_cast h2
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
        simp [ha0, hb, hc, hd1]
    · exact (entries_contra (a := a) (b := b) (c := c) (d := d) (t := t)
        (As := As) (Ds := Ds) ht (by rw [hb]; norm_num) ha0 hAs hAs_pos hle hquad hDs).elim

/-- The eight "grazing" elements of `SL(2,ℤ)`. -/
def isGrazeElem (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Prop :=
  γ = ModularGroup.T * ModularGroup.S * ModularGroup.T
    ∨ γ = -(ModularGroup.T * ModularGroup.S * ModularGroup.T)
    ∨ γ = (ModularGroup.T * ModularGroup.S)⁻¹
    ∨ γ = -((ModularGroup.T * ModularGroup.S)⁻¹)
    ∨ γ = (ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹
    ∨ γ = -((ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹)
    ∨ γ = ModularGroup.S * ModularGroup.T
    ∨ γ = -(ModularGroup.S * ModularGroup.T)

/-- The imaginary axis point `t` and a translate: the two real equations. -/
lemma arcT_entries {γ : SL(2,ℤ)} {t : ℝ} (ht : 0 < t) (hle : t ≤ 1)
    (hτ : γ • Work.Kernels.imagAxis t ht ∈ closure arcT) :
    ((γ 0 1 : ℤ) : ℝ) = (γ • Work.Kernels.imagAxis t ht).re * (γ 1 1 : ℤ)
        - (γ • Work.Kernels.imagAxis t ht).im * (γ 1 0 : ℤ) * t ∧
      ((γ 0 0 : ℤ) : ℝ) * t = (γ • Work.Kernels.imagAxis t ht).re * (γ 1 0 : ℤ) * t
        + (γ • Work.Kernels.imagAxis t ht).im * (γ 1 1 : ℤ) :=
  entries_of_smul_imagAxis' ht _ rfl

/-- **Classification of the coincidence points of the tangency region.** -/
theorem arcT_orbit_classification (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (t : ℝ)
    (ht : 0 < t) (hle : t ≤ 1)
    (hτ : γ • Work.Kernels.imagAxis t ht ∈ closure arcT) :
    isGrazeElem γ := by
  set τ : ℍ := γ • Work.Kernels.imagAxis t ht with hτdef
  have hτ' : τ ∈ closure arcT := hτ
  have hcl := closure_arcT_subset_arcCl hτ'
  have hrene : τ.re ≠ 0 := arcCl_re_ne_zero hcl
  obtain ⟨hre1, hre2, hn1, hn2, harc, hlo, hhi⟩ := hcl
  have hentries := arcT_entries ht hle hτ
  obtain ⟨hR, hI⟩ := hentries
  rw [← hτdef] at hR hI
  have hdet : (γ 0 0 : ℤ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
    have hh := γ.2; rw [Matrix.det_fin_two] at hh; exact hh
  obtain ⟨hA, hB, hIm⟩ := key_identities ht hR hI hdet
  -- τ is not in the interior domain
  have hnotD : τ ∉ DomainD := by
    intro hD
    have h2 : ((γ⁻¹ • τ : ℍ) : ℂ).re = 0 := by
      rw [show (γ⁻¹ • τ : ℍ) = Work.Kernels.imagAxis t ht by
        rw [hτdef, inv_smul_smul]]
      simp [Work.Kernels.imagAxis]
    have := orbit_imagAxis_of_mem_DomainD τ hD γ⁻¹ h2
    exact hrene this
  have hDconds : τ.re = -1 ∨ τ.re = 1 ∨ ‖(τ:ℂ) - (1/2:ℂ)‖ = 1/2
      ∨ ‖(τ:ℂ) + (1/2:ℂ)‖ = 1/2 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hne1, hne2, hne3, hne4⟩ := hcon
    exact hnotD ⟨lt_of_le_of_ne hre1 (Ne.symm hne1), lt_of_le_of_ne hre2 hne2,
      lt_of_le_of_ne hn1 (Ne.symm hne3), lt_of_le_of_ne hn2 (Ne.symm hne4)⟩
  -- the "on-arc" condition
  have honarc : ((γ 0 0 : ℤ):ℝ)^2*t^2 + ((γ 0 1 : ℤ):ℝ)^2
        = ((γ 0 0 : ℤ):ℝ)*((γ 1 0 : ℤ):ℝ)*t^2 + ((γ 0 1 : ℤ):ℝ)*((γ 1 1 : ℤ):ℝ)
      ∨ ((γ 0 0 : ℤ):ℝ)^2*t^2 + ((γ 0 1 : ℤ):ℝ)^2
        = -(((γ 0 0 : ℤ):ℝ)*((γ 1 0 : ℤ):ℝ)*t^2 + ((γ 0 1 : ℤ):ℝ)*((γ 1 1 : ℤ):ℝ)) := by
    have hDpos : 0 < ((γ 1 0 : ℤ):ℝ)^2*t^2 + ((γ 1 1 : ℤ):ℝ)^2 := by
      have h := hIm; nlinarith [h, ht, τ.im_pos]
    rcases hDconds with h | h | h | h
    · -- τ.re = -1 : impossible
      exfalso
      have hnsq' : Complex.normSq (τ:ℂ) = τ.re^2 + τ.im^2 := by
        rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; ring
      have himS : (ModularGroup.S • τ).im = τ.im / (τ.re^2 + τ.im^2) := by
        rw [← UpperHalfPlane.coe_im, UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk,
          Complex.inv_im, Complex.neg_im, Complex.normSq_neg, UpperHalfPlane.coe_im, hnsq']
        ring
      have hnsq : τ.re^2 + τ.im^2 = 1 + τ.im^2 := by rw [h]; ring
      rw [himS, hnsq] at hlo hhi
      have hone : τ.im = 1 := by
        have h2 : (1:ℝ)/2 ≤ τ.im/(1+τ.im^2) := hlo
        rw [le_div_iff₀ (by positivity)] at h2
        nlinarith [sq_nonneg (τ.im - 1)]
      have hd1 : ‖(τ:ℂ) - (1/2:ℂ)‖^2 = 13/4 := by
        rw [arcCl_normSq_sub, h]; rw [hone]; norm_num
      have hd2 : ‖(τ:ℂ) + (1/2:ℂ)‖^2 = 5/4 := by
        rw [arcCl_normSq_add, h]; rw [hone]; norm_num
      rcases harc with hc | hc
      · nlinarith [norm_nonneg ((τ:ℂ) - (1/2:ℂ)), hd1, hc]
      · nlinarith [norm_nonneg ((τ:ℂ) + (1/2:ℂ)), hd2, hc]
    · -- τ.re = 1 : impossible
      exfalso
      have hnsq' : Complex.normSq (τ:ℂ) = τ.re^2 + τ.im^2 := by
        rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; ring
      have himS : (ModularGroup.S • τ).im = τ.im / (τ.re^2 + τ.im^2) := by
        rw [← UpperHalfPlane.coe_im, UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk,
          Complex.inv_im, Complex.neg_im, Complex.normSq_neg, UpperHalfPlane.coe_im, hnsq']
        ring
      have hnsq : τ.re^2 + τ.im^2 = 1 + τ.im^2 := by rw [h]; ring
      rw [himS, hnsq] at hlo hhi
      have hone : τ.im = 1 := by
        have h2 : (1:ℝ)/2 ≤ τ.im/(1+τ.im^2) := hlo
        rw [le_div_iff₀ (by positivity)] at h2
        nlinarith [sq_nonneg (τ.im - 1)]
      have hd1 : ‖(τ:ℂ) - (1/2:ℂ)‖^2 = 5/4 := by
        rw [arcCl_normSq_sub, h]; rw [hone]; norm_num
      have hd2 : ‖(τ:ℂ) + (1/2:ℂ)‖^2 = 13/4 := by
        rw [arcCl_normSq_add, h]; rw [hone]; norm_num
      rcases harc with hc | hc
      · nlinarith [norm_nonneg ((τ:ℂ) - (1/2:ℂ)), hd1, hc]
      · nlinarith [norm_nonneg ((τ:ℂ) + (1/2:ℂ)), hd2, hc]
    · -- |τ - 1/2| = 1/2  ⟹  |τ|² = τ.re ⟹ A = B
      left
      have h2 : ‖(τ:ℂ) - (1/2:ℂ)‖^2 = 1/4 := by rw [h]; norm_num
      have h3 : τ.re^2 + τ.im^2 = τ.re := by
        have h4 : ‖(τ:ℂ) - (1/2:ℂ)‖^2 = τ.re^2 - τ.re + τ.im^2 + 1/4 := arcCl_normSq_sub
        linarith [h2, h4]
      rw [hA, hB, h3]
    · -- |τ + 1/2| = 1/2 ⟹ |τ|² = -τ.re ⟹ A = -B
      right
      have h2 : ‖(τ:ℂ) + (1/2:ℂ)‖^2 = 1/4 := by rw [h]; norm_num
      have h3 : τ.re^2 + τ.im^2 = -τ.re := by
        have h4 : ‖(τ:ℂ) + (1/2:ℂ)‖^2 = τ.re^2 + τ.re + τ.im^2 + 1/4 := arcCl_normSq_add
        linarith [h2, h4]
      rw [hA, hB, h3]
      ring
  -- the `S`-imaginary-part condition
  have hImScond : (1:ℝ)/2 ≤ t/(((γ 0 0 : ℤ):ℝ)^2*t^2 + ((γ 0 1 : ℤ):ℝ)^2) ∧
      t/(((γ 0 0 : ℤ):ℝ)^2*t^2 + ((γ 0 1 : ℤ):ℝ)^2) ≤ 2 := by
    have hnsq' : Complex.normSq (τ:ℂ) = τ.re^2 + τ.im^2 := by
      rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]; ring
    have himS : (ModularGroup.S • τ).im = τ.im / (τ.re^2 + τ.im^2) := by
      rw [← UpperHalfPlane.coe_im, UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk,
        Complex.inv_im, Complex.neg_im, Complex.normSq_neg, UpperHalfPlane.coe_im, hnsq']
      ring
    have hDpos : 0 < ((γ 1 0 : ℤ):ℝ)^2*t^2 + ((γ 1 1 : ℤ):ℝ)^2 := by
      have h := hIm; nlinarith [h, ht, τ.im_pos]
    have hden : (0:ℝ) < τ.re^2+τ.im^2 := by positivity
    have hratio : τ.im / (τ.re^2+τ.im^2)
        = t/(((γ 0 0 : ℤ):ℝ)^2*t^2 + ((γ 0 1 : ℤ):ℝ)^2) := by
      have hnum_pos : (0:ℝ) < ((γ 0 0 : ℤ):ℝ)^2*t^2 + ((γ 0 1 : ℤ):ℝ)^2 := by
        rw [hA]; positivity
      rw [div_eq_div_iff (ne_of_gt hden) (ne_of_gt hnum_pos)]
      rw [hA]
      nlinarith [hIm]
    have hval : (ModularGroup.S • τ).im
        = t/(((γ 0 0 : ℤ):ℝ)^2*t^2 + ((γ 0 1 : ℤ):ℝ)^2) := by rw [himS, hratio]
    exact ⟨hval ▸ hlo, hval ▸ hhi⟩
  -- conclude by the entry-level classification
  have hgraze := entries_classification ht hle hA hB hIm τ.im_pos hdet honarc hImScond
  rcases hgraze with ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ |
    ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ |
    ⟨ha, hb, hc, hd⟩
  · refine Or.inl ?_
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_T, ModularGroup.coe_S,
        Matrix.SpecialLinearGroup.coe_neg, ha, hb, hc, hd]
  · refine Or.inr (Or.inl ?_)
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_T, ModularGroup.coe_S,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg, ha, hb, hc, hd]
  · refine Or.inr (Or.inr (Or.inl ?_))
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_T, ModularGroup.coe_S,
        Matrix.SpecialLinearGroup.coe_neg, ha, hb, hc, hd]
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_T, ModularGroup.coe_S,
        Matrix.SpecialLinearGroup.coe_neg, ha, hb, hc, hd]
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_T, ModularGroup.coe_S,
        Matrix.SpecialLinearGroup.coe_neg, ha, hb, hc, hd]
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_T, ModularGroup.coe_S,
        Matrix.SpecialLinearGroup.coe_neg, ha, hb, hc, hd]
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_T, ModularGroup.coe_S,
        Matrix.SpecialLinearGroup.coe_neg, ha, hb, hc, hd]
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_T, ModularGroup.coe_S,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg, ha, hb, hc, hd]

/-! ## The tangency region: boundedness, compactness, and the two arc elements -/

/-- `arcT` is bounded (in the hyperbolic metric of `ℍ`). -/
lemma isBounded_arcT : Bornology.IsBounded (arcT : Set ℍ) := by
  rw [Metric.isBounded_iff_subset_closedBall (UpperHalfPlane.I)]
  refine ⟨13, fun z hz => ?_⟩
  rw [Metric.mem_closedBall]
  have h1 : dist z UpperHalfPlane.I
      ≤ ‖(z:ℂ) - Complex.I‖ / Real.sqrt (z.im * 1) := by
    have := UpperHalfPlane.dist_le_dist_coe_div_sqrt z UpperHalfPlane.I
    simpa [UpperHalfPlane.coe_I, UpperHalfPlane.I_im, dist_eq_norm] using this
  have h2 : ‖(z:ℂ) - Complex.I‖ ≤ 4 := by
    have h := arcT_norm_le hz
    calc ‖(z:ℂ) - Complex.I‖ ≤ ‖(z:ℂ)‖ + ‖(Complex.I:ℂ)‖ := norm_sub_le _ _
      _ = ‖(z:ℂ)‖ + 1 := by rw [Complex.norm_I]
      _ ≤ 3 + 1 := by linarith
      _ = 4 := by norm_num
  have h4 : (1:ℝ)/10 < z.im := arcT_im_gt hz
  have h5 : (0:ℝ) < Real.sqrt (z.im * 1) := Real.sqrt_pos.mpr (by linarith)
  have h6 : (4:ℝ)/13 ≤ Real.sqrt (z.im * 1) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    nlinarith
  calc dist z UpperHalfPlane.I
      ≤ ‖(z:ℂ) - Complex.I‖ / Real.sqrt (z.im * 1) := h1
    _ ≤ 4 / ((4:ℝ)/13) := by
        rw [div_le_div_iff₀ h5 (by norm_num)]
        nlinarith
    _ = 13 := by norm_num

/-- The closure of `arcT` is compact. -/
lemma isCompact_closure_arcT : IsCompact (closure (arcT : Set ℍ)) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, isBounded_arcT.closure⟩

/-- The `i`-images of the four grazing elements. -/
lemma graze_I_eq (δ : SL(2, ℤ)) (hδ : Graze.GrazeElem δ) :
    δ • UpperHalfPlane.I = Graze.cR ∨ δ • UpperHalfPlane.I = Graze.cL := by
  have hne : ((1:ℂ) - Complex.I) ≠ 0 := by
    intro hh; have := congrArg Complex.im hh; simp at this
  rcases hδ with h | h | h | h <;> subst h
  · exact Or.inl rfl
  · refine Or.inl ?_
    apply UpperHalfPlane.ext
    rw [Graze.coe_TS_inv_smul, Graze.cR_coe, UpperHalfPlane.coe_I]
    rw [div_eq_div_iff hne (by norm_num)]
    ring_nf
    rw [Complex.I_sq]
    ring
  · exact Or.inr rfl
  · refine Or.inr ?_
    apply UpperHalfPlane.ext
    rw [Graze.coe_TST_inv_smul, Graze.cL_coe, UpperHalfPlane.coe_I]
    rw [div_eq_div_iff hne (by norm_num)]
    ring_nf
    rw [Complex.I_sq]
    ring

/-- Every grazing element (of either sign) becomes a "positive" one with the same action. -/
lemma isGrazeElem_exists (γ : SL(2, ℤ)) (h : isGrazeElem γ) :
    ∃ δ : SL(2, ℤ), Graze.GrazeElem δ ∧ ∀ z : ℍ, δ • z = γ • z := by
  rcases h with h | h | h | h | h | h | h | h
  · exact ⟨_, Or.inl h, fun z => by rw [h]⟩
  · exact ⟨ModularGroup.T * ModularGroup.S * ModularGroup.T, Or.inl rfl,
      fun z => by rw [h, ModularGroup.SL_neg_smul]⟩
  · exact ⟨_, Or.inr (Or.inl h), fun z => by rw [h]⟩
  · exact ⟨(ModularGroup.T * ModularGroup.S)⁻¹, Or.inr (Or.inl rfl),
      fun z => by rw [h, ModularGroup.SL_neg_smul]⟩
  · exact ⟨_, Or.inr (Or.inr (Or.inr h)), fun z => by rw [h]⟩
  · exact ⟨(ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹, Or.inr (Or.inr (Or.inr rfl)),
      fun z => by rw [h, ModularGroup.SL_neg_smul]⟩
  · exact ⟨_, Or.inr (Or.inr (Or.inl h)), fun z => by rw [h]⟩
  · exact ⟨ModularGroup.S * ModularGroup.T, Or.inr (Or.inr (Or.inl rfl)),
      fun z => by rw [h, ModularGroup.SL_neg_smul]⟩

/-- The Möbius action of a fixed element is locally Lipschitz. -/
lemma exists_lipschitz_smul (γ : SL(2, ℤ)) (z₀ : ℍ) :
    ∃ δZ cZ : ℝ, 0 < δZ ∧ 0 < cZ ∧ ∀ z : ℍ,
      ‖(z:ℂ) - (z₀:ℂ)‖ < δZ →
      ‖((γ • z : ℍ) : ℂ) - ((γ • z₀ : ℍ) : ℂ)‖ ≤ cZ * ‖(z:ℂ) - (z₀:ℂ)‖ := by
  set c : ℂ := (((γ 1 0 : ℤ) : ℝ) : ℂ) with hc
  set d : ℂ := (((γ 1 1 : ℤ) : ℝ) : ℂ) with hd
  have hden0 : c * (z₀:ℂ) + d ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    rw [hc, hd] at him hre
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_im, Complex.add_re, Complex.mul_re, Complex.zero_re, UpperHalfPlane.coe_im,
      UpperHalfPlane.coe_re, mul_zero, zero_mul, add_zero] at him hre
    have hc0 : γ 1 0 = 0 := by
      have : ((γ 1 0 : ℤ) : ℝ) = 0 := by
        rcases mul_eq_zero.mp him with h1 | h1
        · exact h1
        · exact absurd h1 (ne_of_gt z₀.im_pos)
      exact_mod_cast this
    have hd0 : γ 1 1 = 0 := by
      have : ((γ 1 1 : ℤ) : ℝ) = 0 := by
        rw [hc0] at hre; simpa using hre
      exact_mod_cast this
    have hdet := γ.2
    rw [Matrix.det_fin_two, hc0, hd0] at hdet
    norm_num at hdet
  have hcont : Continuous (fun z : ℂ => c * z + d) :=
    (continuous_const.mul continuous_id).add continuous_const
  obtain ⟨δZ, hδZ, hδZb⟩ := Metric.continuousAt_iff.mp hcont.continuousAt (‖c * (z₀:ℂ) + d‖/2)
    (by positivity)
  refine ⟨δZ, 2 / ‖c * (z₀:ℂ) + d‖^2, hδZ, by positivity, fun z hz => ?_⟩
  have hw : (0:ℝ) < ‖c * (z₀:ℂ) + d‖ := by positivity
  have hsub : ‖c * ((z:ℂ) - (z₀:ℂ))‖ < ‖c * (z₀:ℂ) + d‖ / 2 := by
    have hb := hδZb (by rw [dist_eq_norm]; exact hz)
    rw [dist_eq_norm, show c * (z:ℂ) + d - (c * (z₀:ℂ) + d) = c * ((z:ℂ) - (z₀:ℂ)) by ring] at hb
    exact hb
  have hdenz : c * (z:ℂ) + d ≠ 0 := by
    intro h0
    have h1 : c * ((z:ℂ) - (z₀:ℂ)) = -(c * (z₀:ℂ) + d) := by
      linear_combination h0
    have h2 := hsub
    rw [h1, norm_neg] at h2
    linarith [hw]
  have hden : ‖c * (z₀:ℂ) + d‖/2 ≤ ‖c * (z:ℂ) + d‖ := by
    have htri : ‖c * (z₀:ℂ) + d‖ ≤ ‖c * (z:ℂ) + d‖ + ‖c * ((z:ℂ) - (z₀:ℂ))‖ := by
      have := norm_sub_le (c * (z:ℂ) + d) (c * ((z:ℂ) - (z₀:ℂ)))
      rw [show c * (z:ℂ) + d - c * ((z:ℂ) - (z₀:ℂ)) = c * (z₀:ℂ) + d by ring] at this
      exact this
    linarith [htri, hsub]
  have hdiff : ((γ • z : ℍ) : ℂ) - ((γ • z₀ : ℍ) : ℂ)
      = ((z:ℂ) - (z₀:ℂ)) / ((c * (z:ℂ) + d) * (c * (z₀:ℂ) + d)) := by
    have hcz : ((algebraMap ℤ ℝ (γ 1 0) : ℝ) : ℂ) * (z:ℂ) + ((algebraMap ℤ ℝ (γ 1 1) : ℝ) : ℂ)
        = c * (z:ℂ) + d := by rw [hc, hd]; simp
    have hcz0 : ((algebraMap ℤ ℝ (γ 1 0) : ℝ) : ℂ) * (z₀:ℂ) + ((algebraMap ℤ ℝ (γ 1 1) : ℝ) : ℂ)
        = c * (z₀:ℂ) + d := by rw [hc, hd]; simp
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_specialLinearGroup_apply,
      hcz, hcz0, div_sub_div _ _ hdenz hden0]
    rw [div_eq_div_iff (mul_ne_zero hdenz hden0) (mul_ne_zero hdenz hden0)]
    have hdetC : ((algebraMap ℤ ℝ (γ 0 0) : ℝ) : ℂ) * ((algebraMap ℤ ℝ (γ 1 1) : ℝ) : ℂ)
        - ((algebraMap ℤ ℝ (γ 0 1) : ℝ) : ℂ) * ((algebraMap ℤ ℝ (γ 1 0) : ℝ) : ℂ) = 1 := by
      have h := γ.2
      rw [Matrix.det_fin_two] at h
      have h2 := congrArg (fun n : ℤ => (((n : ℝ) : ℂ))) h
      push_cast at h2
      simpa using h2
    linear_combination hdetC * ((z:ℂ) - (z₀:ℂ)) * ((c * (z:ℂ) + d) * (c * (z₀:ℂ) + d))
  rw [hdiff, norm_div, norm_mul]
  calc ‖(z:ℂ) - (z₀:ℂ)‖ / (‖c * (z:ℂ) + d‖ * ‖c * (z₀:ℂ) + d‖)
      ≤ ‖(z:ℂ) - (z₀:ℂ)‖ / ((‖c * (z₀:ℂ) + d‖/2) * ‖c * (z₀:ℂ) + d‖) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (by nlinarith [hden, hw])
    _ = 2 / ‖c * (z₀:ℂ) + d‖^2 * ‖(z:ℂ) - (z₀:ℂ)‖ := by
        field_simp


/-- The kernel is bounded on the "middle range" `ε ≤ t ≤ 1` for `τ ∈ closure arcT`. -/
theorem arcT_middle (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ : UpperHalfPlane) (t : ℝ), τ ∈ closure arcT → ε ≤ t → t ≤ 1 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := by
  have hK : IsCompact (closure (arcT : Set ℍ)) := isCompact_closure_arcT
  have hP : IsCompact (KaxisMid.Pspace (closure arcT) ε) := KaxisMid.isCompact_Pspace hK ε
  have hloc : ∀ p : KaxisMid.Pspace (closure arcT) ε, ∃ C : ℝ,
      0 < C ∧ ∃ r : ℝ, 0 < r ∧ ∀ (q : KaxisMid.Pspace (closure arcT) ε),
        ‖((q.1).1 : ℂ) - ((p.1).1 : ℂ)‖ < r → |(q.1).2 - (p.1).2| < r →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (q.1).1 (q.1).2‖ ≤ C := by
    intro p
    obtain ⟨hpK, hpε, hp1⟩ := KaxisMid.mem_Pspace.mp p.2
    by_cases hcoin : Work.Kernels.jInvariantFun (p.1).1
        = Work.Kernels.jInvariantFun (KaxisMid.pz hε (p.1) p.2)
    · -- a coincidence
      have hpt : 0 < (p.1).2 := lt_of_lt_of_le hε hpε
      have hpzeq : KaxisMid.pz hε (p.1) p.2 = Work.Kernels.imagAxis (p.1).2 hpt :=
        UpperHalfPlane.ext rfl
      obtain ⟨γ, hγ⟩ := jInvariantFun_eq_smul_of_eq hcoin
      have hτcl : γ • Work.Kernels.imagAxis (p.1).2 hpt ∈ closure arcT := by
        rw [← hpzeq, hγ]; exact hpK
      have hgraze := arcT_orbit_classification γ (p.1).2 hpt hp1 hτcl
      obtain ⟨δ, hδg, hδact⟩ := isGrazeElem_exists γ hgraze
      have hδp : δ • (KaxisMid.pz hε (p.1) p.2) = (p.1).1 := by
        rw [hδact, hγ]
      by_cases ht1 : (p.1).2 = 1
      · -- `t = 1`: the point is a tangency point of `𝒟`
        have hI : δ • UpperHalfPlane.I = (p.1).1 := by
          rw [← hδp]
          congr 1
          apply UpperHalfPlane.ext
          rw [KaxisMid.pz_coe, ht1, UpperHalfPlane.coe_I]
          norm_num
        have hpp : KaxisMid.pz hε (p.1) p.2 = UpperHalfPlane.I := by
          apply UpperHalfPlane.ext
          rw [KaxisMid.pz_coe, ht1, UpperHalfPlane.coe_I]
          norm_num
        rcases graze_I_eq δ hδg with hδR | hδL
        · obtain ⟨ρ, C', hρ, hC', hkey⟩ := Graze.key_bound_arc ℓ d hd
            (ModularGroup.T * ModularGroup.S * ModularGroup.T) (Or.inl rfl)
          refine ⟨max C' 1, lt_of_lt_of_le one_pos (le_max_right C' 1), ρ, hρ, ?_⟩
          intro q hq1 hq2
          rw [KaxisMid.Kaxis_eq_Kfun_pz (ℓ := ℓ) (d := d) hε q.2]
          refine le_trans (hkey (q.1).1 (KaxisMid.pz hε (q.1) q.2) ?_ ?_) (le_max_left C' 1)
          · have hA : ((ModularGroup.T * ModularGroup.S * ModularGroup.T) • UpperHalfPlane.I : ℍ)
                = (p.1).1 := by
              rw [← hI, hδR]
              rfl
            rw [hA]; exact hq1
          · rw [← UpperHalfPlane.coe_I, ← hpp, KaxisMid.norm_pz_sub hε q.2 p.2]
            exact hq2
        · obtain ⟨ρ, C', hρ, hC', hkey⟩ := Graze.key_bound_arc ℓ d hd
            (ModularGroup.S * ModularGroup.T) (Or.inr rfl)
          refine ⟨max C' 1, lt_of_lt_of_le one_pos (le_max_right C' 1), ρ, hρ, ?_⟩
          intro q hq1 hq2
          rw [KaxisMid.Kaxis_eq_Kfun_pz (ℓ := ℓ) (d := d) hε q.2]
          refine le_trans (hkey (q.1).1 (KaxisMid.pz hε (q.1) q.2) ?_ ?_) (le_max_left C' 1)
          · have hA : ((ModularGroup.S * ModularGroup.T) • UpperHalfPlane.I : ℍ) = (p.1).1 := by
              rw [← hI, hδL]
              rfl
            rw [hA]; exact hq1
          · rw [← UpperHalfPlane.coe_I, ← hpp, KaxisMid.norm_pz_sub hε q.2 p.2]
            exact hq2
      · -- `t ≠ 1`: the pole on the branch is removable
        obtain ⟨C', hC', r, hr, H⟩ := KaxisMid.exists_local_bound_branch_aux ℓ d hd hK hε (p.1) p.2 ht1
          (Z := fun τ : ℍ => δ⁻¹ • τ)
          (by rw [← hδp, ← mul_smul, inv_mul_cancel, one_smul])
          (by intro τ
              have h := Graze.graze_vanish ℓ d hd δ hδg (δ⁻¹ • τ)
              rwa [← mul_smul, mul_inv_cancel, one_smul] at h)
          (by intro τ; exact jInvariantFun_smul_of_slash δ⁻¹ τ)
          (by
            obtain ⟨δZ, cZ, hδZ, hcZ, hb⟩ := exists_lipschitz_smul δ⁻¹ (p.1).1
            exact ⟨δZ, cZ, hδZ, hcZ, hb⟩)
        refine ⟨C', hC', r, hr, ?_⟩
        intro q hq1 hq2
        rw [KaxisMid.Kaxis_eq_Kfun_pz (ℓ := ℓ) (d := d) hε q.2]
        exact H q.1 q.2 hq1 hq2
    · -- no coincidence
      obtain ⟨C, hC, r, hr, H⟩ := KaxisMid.exists_local_bound_clean ℓ d hd hK hε (p.1) p.2
        (fun h => hcoin h)
      refine ⟨C, hC, r, hr, ?_⟩
      intro q hq1 hq2
      rw [KaxisMid.Kaxis_eq_Kfun_pz (ℓ := ℓ) (d := d) hε q.2]
      refine H (q.1) q.2 hq1 ?_
      rw [KaxisMid.norm_pz_sub hε q.2 p.2]
      exact hq2
  classical
  let Cf : KaxisMid.Pspace (closure arcT) ε → ℝ := fun p => Classical.choose (hloc p)
  have hCfpos : ∀ p, 0 < Cf p := fun p => (Classical.choose_spec (hloc p)).1
  let rf : KaxisMid.Pspace (closure arcT) ε → ℝ :=
    fun p => Classical.choose (Classical.choose_spec (hloc p)).2
  have hrfpos : ∀ p, 0 < rf p :=
    fun p => (Classical.choose_spec (Classical.choose_spec (hloc p)).2).1
  have hbound : ∀ (p q : KaxisMid.Pspace (closure arcT) ε),
      ‖((q.1).1 : ℂ) - ((p.1).1 : ℂ)‖ < rf p → |(q.1).2 - (p.1).2| < rf p →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (q.1).1 (q.1).2‖ ≤ Cf p :=
    fun p => (Classical.choose_spec (Classical.choose_spec (hloc p)).2).2
  have hopen : ∀ p : KaxisMid.Pspace (closure arcT) ε, IsOpen {q : ℍ × ℝ |
      ‖(q.1 : ℂ) - ((p.1).1 : ℂ)‖ < rf p ∧ |q.2 - (p.1).2| < rf p} := by
    intro p
    have h1 : IsOpen {q : ℍ × ℝ | ‖(q.1 : ℂ) - ((p.1).1 : ℂ)‖ < rf p} :=
      isOpen_lt (Continuous.norm ((UpperHalfPlane.continuous_coe.comp continuous_fst).sub
        continuous_const)) continuous_const
    have h2 : IsOpen {q : ℍ × ℝ | |q.2 - (p.1).2| < rf p} :=
      isOpen_lt (continuous_snd.sub continuous_const).abs continuous_const
    exact h1.inter h2
  have hcover : KaxisMid.Pspace (closure arcT) ε ⊆ ⋃ p : KaxisMid.Pspace (closure arcT) ε,
      {q : ℍ × ℝ | ‖(q.1 : ℂ) - ((p.1).1 : ℂ)‖ < rf p ∧ |q.2 - (p.1).2| < rf p} := by
    intro q hq
    refine Set.mem_iUnion.mpr ⟨⟨q, hq⟩, ?_⟩
    exact ⟨by simpa using hrfpos ⟨q, hq⟩, by simpa using hrfpos ⟨q, hq⟩⟩
  obtain ⟨s, hs⟩ := hP.elim_finite_subcover
    (fun p : KaxisMid.Pspace (closure arcT) ε => {q : ℍ × ℝ |
      ‖(q.1 : ℂ) - ((p.1).1 : ℂ)‖ < rf p ∧ |q.2 - (p.1).2| < rf p})
    hopen hcover
  have hsum : (0:ℝ) < (∑ p ∈ s, Cf p) + 1 := by
    have := Finset.sum_nonneg (s := s) (f := Cf) (fun p _ => (hCfpos p).le)
    linarith
  refine ⟨(∑ p ∈ s, Cf p) + 1, hsum, fun τ t hτT hεt ht1 => ?_⟩
  have hq : (τ, t) ∈ KaxisMid.Pspace (closure arcT) ε := ⟨hτT, hεt, ht1⟩
  have hmem := hs hq
  rw [Set.mem_iUnion₂] at hmem
  obtain ⟨p, hps, hpU⟩ := hmem
  have hle := hbound p ⟨(τ, t), hq⟩ hpU.1 hpU.2
  refine le_trans hle ?_
  have := Finset.single_le_sum (s := s) (f := Cf) (fun x _ => (hCfpos x).le) hps
  linarith


theorem arcT_flat (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ N : ℝ, 0 ≤ N → ∃ c : ℝ, 0 < c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ Work.Asymptotics.arcT → 0 < t → t ≤ 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ c * t ^ N := by
  intro N hN
  obtain ⟨δ, hδ, hcusp⟩ := HalfFunnel.Kaxis_cusp_of_bounded ℓ d hd isBounded_arcT
  obtain ⟨c1, hc1, hcusp'⟩ := hcusp N hN
  have hε : 0 < min δ (1/2) := lt_min hδ (by norm_num)
  obtain ⟨C, hC, hmid⟩ := arcT_middle ℓ d hd hε
  refine ⟨max c1 (C * (min δ (1/2)) ^ (-N)), ?_, fun τ t hτ ht ht1 => ?_⟩
  · exact lt_of_lt_of_le hc1 (le_max_left _ _)
  · by_cases hlt : t ≤ min δ (1/2)
    · refine le_trans (hcusp' τ t hτ ht (le_trans hlt (min_le_left _ _))) ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ht.le N)
    · rw [not_le] at hlt
      have h1 : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C :=
        hmid τ t (subset_closure hτ) (le_of_lt hlt) ht1
      have h2 : (min δ (1/2)) ^ N ≤ t ^ N := Real.rpow_le_rpow hε.le (le_of_lt hlt) hN
      have h3 : C ≤ C * (min δ (1/2)) ^ (-N) * t ^ N := by
        have h4 : C * (min δ (1/2)) ^ (-N) * (min δ (1/2)) ^ N
            ≤ C * (min δ (1/2)) ^ (-N) * t ^ N :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hC.le (Real.rpow_nonneg hε.le _))
        have h5 : C * (min δ (1/2)) ^ (-N) * (min δ (1/2)) ^ N = C := by
          rw [mul_assoc, ← Real.rpow_add hε, neg_add_cancel, Real.rpow_zero, mul_one]
        linarith [h4, h5.le, h5.ge]
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := h1
        _ ≤ C * (min δ (1/2)) ^ (-N) * t ^ N := h3
        _ ≤ max c1 (C * (min δ (1/2)) ^ (-N)) * t ^ N :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le N)


end Work.Asymptotics
