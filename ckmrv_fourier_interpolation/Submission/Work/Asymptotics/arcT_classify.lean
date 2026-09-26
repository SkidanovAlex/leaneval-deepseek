/-
# The orbit classification of the tangency-arc region (cusp-side copy)

If `γ • (i t)` lies in the closure of `arcT` for `t ≤ 1`, then `γ` is one of the eight
"grazing" elements `T S T`, `(T S)⁻¹`, `S T`, `(T S T)⁻¹`, up to sign.

This is `Work.Asymptotics.arcT_orbit_classification` together with its elementary geometric
and algebraic prerequisites, reproduced under the namespace `ArcClassify` so that it lives on
the *clean* side of the workspace: the original lives in `arcT_flat.lean`, whose transitive
`KPlusXiDefs` dependency cannot be co-imported with the `CuspExp` expansion machinery used by
`arcT_tail` (both `KPlusXiDefs` and `MiddleRange.Main` define
`Work.Asymptotics.continuous_jInvariantFun`).
-/
import Mathlib
import Submission.Work.Asymptotics.arcRegion
import Submission.Work.Asymptotics.orbit_imagAxis_of_mem_DomainD

noncomputable section

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups UpperHalfPlane Topology

set_option maxHeartbeats 3200000

namespace Work.Asymptotics.ArcClassify
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

end Work.Asymptotics.ArcClassify

namespace Work.Asymptotics.ArcClassify

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

end Work.Asymptotics.ArcClassify

namespace Work.Asymptotics.ArcClassify

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

end Work.Asymptotics.ArcClassify
